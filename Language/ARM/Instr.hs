{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# OPTIONS_GHC -funbox-strict-fields #-}
module Language.ARM.Instr where

import Text.Cassette hiding (C, CC, CC0, BinL)
import qualified Text.Cassette as Cassette
import qualified Data.ByteString.Lazy.Char8 as B
import qualified Control.Applicative
import Language.Literals.Binary
import Data.Word
import Data.Bits
import Data.Maybe (fromMaybe)


type Register = Int

data Shift = LSL !Int | LSR !Int | ASR !Int | ROR !Int | RRX
           deriving (Eq, Show)

data Operand = R !Register         -- ^ Register
             | I !Word32           -- ^ Immediate data
             | S !Shift            -- ^ Operand shift
             deriving (Eq, Show)

type Opcode = Word32
type Mnemonic = B.ByteString

-- | Unpacked instruction.
data Instruction = Mnemonic :$ [Operand]
                 deriving (Eq, Show)

mask :: Bits a => Int -> Int -> a
mask start end | start < end = 0
mask start end = complement (complement 0 `shiftL` (start - end + 1)) `shiftL` end

range :: Bits a => Int -> Int -> a -> a
range start end _ | start < end = 0
range start end w = (mask start end .&. w) `shiftR` end

setRangeC :: Bits s => Int -> Int -> s -> Cassette.C s r -> Cassette.C s r
setRangeC start end _   | start < end =
  sideA nothing
setRangeC start end src | complement (mask (start - end) 0) .&. src /= 0 =
  sideA empty
setRangeC start end src =
  \k k' s -> k k' $ (src `shiftL` end) .|. complement (mask start end) .&. s

setRange :: Bits a => Int -> Int -> a -> a -> a
setRange start end src dst =
  fromMaybe err $ setRangeC start end src (const Just) (const Nothing) dst
  where err = error "setRange: operand does not fit in range."

type C r  = Cassette.C   Opcode r
type CC a = Cassette.CC  Opcode a
type CC0  = Cassette.CC0 Opcode
type BinL a b c = Cassette.BinL Opcode a b c
type CCC a = forall r r'. K7 (C (a -> r)) (C (a -> r)) (C (a -> r')) (C (a -> r'))

instructionL :: BinL Mnemonic [Operand] Instruction
instructionL = K7 f g where
  f k k' s args mnem = k (\s _ -> k' s args mnem) s (mnem :$ args)
  g k k' s t@(mnem :$ args) = k (\s _ _ -> k' s t) s args mnem

-- | Encoder successful only if predicate holds.
guard :: (a -> Bool) -> CCC a
guard p = K7 id g where
  g k k' s x | p x = k k' s x
             | otherwise = k' s x

mnem :: B.ByteString -> CC Mnemonic
mnem name = K7 f g where
  f k k' s = k (\s _ -> k' s) s name
  g k k' s x | name `B.isPrefixOf` x = k (\s -> k' s x) s
             | otherwise = k' s x

args :: [CC Operand] -> CC [Operand]
args [] = nilL
args (x:xs) = consL --> x <> args xs

-- | Do nothing if true, fail if false.
when :: Bool -> CC0
when True = nothing
when False = empty

status :: CCC Mnemonic
status = K7 f g where
  f k k' s x | (s `shiftR` 16) `testBit` 4 = k k' s (insert 3 "S" x)
             | otherwise = k k' s x
  g k k' s x | B.length x > 3,
               x `B.index` 3 == 'S' = k k' (s `setBit` 4) x
             | otherwise = k k' s x
  insert i xs ys | (beg, end) <- B.splitAt i ys = beg `B.append` xs `B.append` end

statusOn :: CCC Mnemonic
statusOn = guard (\name -> name `B.index` 3 == 'S')

statusOff :: CCC Mnemonic
statusOff = guard (\name -> name `B.index` 3 /= 'S')

data Part = Lo | Hi
          deriving Enum

sign :: Part -> Int -> Int -> Word32 -> CC0
sign which start end bits = K7 f g where
  f k k' s | range (start + base) (end + base) s == bits = k k' s
           | otherwise = k' s
  g k k' s = k k' (setRange (start + base) (end + base) bits s)
  base = fromEnum which `shiftL` 4

imm12 :: CC Operand
imm12 = K7 f g where
  f k k' s = k (\s _ -> k' s) s (I x) where
    imm = (range 26 26 s `shiftL` 11) .|. (range 14 12 s `shiftL` 8) .|. range 7 0 s
    n = range 7 0 imm
    x = case range 11 8 imm of
          [b|0000|] -> n
          [b|0001|] -> n `shiftL` 16 .|. n
          [b|0010|] -> n `shiftL` 24 .|. n `shiftL` 8
          [b|0011|] -> n `shiftL` 24 .|. n `shiftL` 16 .|. n `shiftL` 8 .|. n
          _         -> (0 `setBit` 7 .|. range 6 0 imm) `rotateR` fromIntegral (range 11 7 imm)
  g k k' s o@(I x) | x <= 0xff = k (\s -> k' s o) (setRange 7 0 x s)
                   | otherwise = k (\s -> k' s o) (explode imm s) where
    explode imm s = setRange 26 26 (range 11 11 imm) $
                    setRange 14 12 (range 10 8 imm) $
                    setRange 7 0 (range 7 0 imm) s
    imm | let octet = range 7 0 x
              mask  = ((0 `shiftL` 8 .|. octet) `shiftL` 8 .|. 0) `shiftL` 8 .|. octet,
          x `xor` mask == 0 = exp [b|0001|] $ base octet 0
        | let octet = range 7 0 x
              mask  = ((octet `shiftL` 8 .|. 0) `shiftL` 8 .|. octet) `shiftL` 8 .|. 0,
          x `xor` mask == 0 = exp [b|0010|] $ base octet 0
        | let octet = range 7 0 x
              mask  = ((octet `shiftL` 8 .|. octet) `shiftL` 8 .|. octet) `shiftL` 8 .|. octet,
          x `xor` mask == 0 = exp [b|0011|] $ base octet 0
        | (i,n):_ <- [ (i,n) | i <- [0..31], let n = x `rotateL` i,
                               complement [b|1111111|] .&. n == [b|10000000|] ] =
          setRange 11 7 (fromIntegral i) $ setRange 6 0 (range 6 0 n) 0
        | otherwise = error "imm12: Cannot represent immediate value."
  base = setRange 7 0
  exp  = setRange 11 8

reg :: Part -> Int -> Int -> CC Operand
reg which start end = K7 f g where
  f k k' s = k (\s _ -> k' s) s (R $ fromIntegral $ range (start + base) (end + base) s)
  -- If register number is already set, then check it is the same, otherwise fail.
  g k k' s o@(R reg) | range (start + base) (end + base) s == fromIntegral reg =
    k (\s -> k' s o) (setRange (start + base) (end + base) (fromIntegral reg) s)
                     | otherwise = k' s o
  base = fromEnum which `shiftL` 4

-- | First operand, destination register, second operand (wide encoding).
regndmW :: [CC Operand]
regndmW = [reg Lo 11 8, reg Hi 3 0, reg Lo 3 0]

-- | Second operand, first operand, destination register (narrow encoding).
regmndN :: [CC Operand]
regmndN = [reg Lo 2 1 0, reg Lo 5 3, reg Lo 8 6]

regndimm12 :: [CC Operand]
regndimm12 = [reg Lo 11 8, reg Hi 3 0, imm12]

regdn :: Int -> Int -> [CC Operand]
regdn start end = [reg Lo start end, reg Lo start end]

regdn_m :: Int -> Int -> Int -> Int -> [CC Operand]
regdn_m startdn enddn startm endm =
  regdn startdn enddn ++ ([reg Lo startm endm] :: [CC Operand])

-- | Register shift.
rshift :: CC Operand
rshift = K7 f g where
  f k k' s = maybe (k' s) (k (\s _ -> k' s) s . S) $
             let typ = range 5 4 s
                 imm = range 14 12 s `shiftL` 2 .|. range 7 6 s
             in case (typ, imm) of
                  ([b|00|], 0) -> Control.Applicative.empty
                  ([b|00|], n) -> return $ LSL (fromIntegral n)
                  ([b|01|], 0) -> return $ LSR 32
                  ([b|01|], n) -> return $ LSR (fromIntegral n)
                  ([b|10|], 0) -> return $ ASR 32
                  ([b|10|], n) -> return $ ASR (fromIntegral n)
                  ([b|11|], 0) -> return $ RRX
                  ([b|11|], n) -> return $ ROR (fromIntegral n)
  g k k' s x@(S sh) =
    k (\s -> k' s x) $ uncurry encode $ case sh of
      LSL n  -> ([b|00|], fromIntegral n)
      LSR 32 -> ([b|01|], 0)
      LSR n  -> ([b|01|], fromIntegral n)
      ASR 32 -> ([b|10|], 0)
      ASR n  -> ([b|10|], fromIntegral n)
      RRX    -> ([b|11|], 0)
      ROR n  -> ([b|11|], fromIntegral n)
    where encode typ imm = setRange 5 4 typ $
                           setRange 14 12 (range 4 2 imm) $
                           setRange 7 6 (range 1 0 imm) s

instruction :: Bool -> CC Instruction
instruction insideIT = instructionL --> variants where
  outsideIT = not insideIT
  variants =
        -- ADC (immediate) encoding T1
        mnem "ADC" <> status <>
        args regndimm12 <>
        sign Hi 15 11 [b|11110|] <> sign Hi 9 5 [b|01010|] <> sign Lo 15 15 [b|0|]

        -- ADC (register) encoding T1
    <|> mnem "ADC" <> (statusOn  <> when outsideIT <|> statusOff <> when insideIT) <>
        args (regdn_m 5 3 2 0) <>
        sign Lo 15 6 [b|0100000101|]

        -- ADC (register) encoding T2
    <|> mnem "ADC" <> status <>
        args regndmW <> optional rshift <>
        sign Hi 15 5 [b|11101011010|]

        -- ADD (immediate) encoding T1
    <|> mnem "ADD" <> (statusOn <> when outsideIT <|> statusOff <> when insideIT) <>
        args regimm3nd <>
        sign Lo 15 9 [b|0001110|]

        -- ADD (immediate) encoding T2
    <|> mnem "ADD" <> (statusOn <> when outsideIT <|> statusOff <> when insideIT) <>
        args [regdn 10 8, imm8] <>
        sign Lo 15 11 [b|00110|]

        -- ADD (immediate) encoding T3
    <|> mnem "ADD" <> status <>
        args regndimm12 <>
        sign Hi 15 11 [b|11110|] <> sign Hi 9 5 [b|01000|] <> sign Lo 15 15 [b|0|]

        -- ADD (immediate) encoding T4
    <|> mnem "ADDW" <>
        args regndimm12 <>
        args 15 11 [b|11110|] <> sign Hi 9 4 [b|00000|] <> sign Lo 15 15 [b|0|]

        -- ADD (register) encoding T1
    <|> mnem "ADD" <> (statusOn <> when outsideIT <|> statusOff <> when insideIT) <>
        args regmndN <>
        sign Lo 15 9 [b|0001100|]

        -- ADD (register) encoding T2
    <|> mnem "ADD" <>
        args regm_dn
        sign Lo 15 8 [b|01000100|]

        -- ADD (register) encoding T3
    <|> mnem "ADD" <> status <>
        args regndmW <> optional rshift <>
        sign Hi 15 5 [b|11101011000|]
