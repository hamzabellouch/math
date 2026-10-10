import OAI.Combinatorics.EditApproximation.Binary.BinaryReductionSpace
import OAI.Combinatorics.EditApproximation.Binary.BinarySeedMedianWork
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Every insertion-sort copy, median traversal, ceiling and final trimming
scan is retained in these seed-branch allocation and call-frame counters. -/

namespace EditApproximation



theorem wordLEAllocation_le_work (a b : List Bool) :
    wordLEAllocation a b ≤ (wordLEWithWork a b).2 := by
  exact Nat.zero_le _



theorem wordInsertAllocation_le_work (a : List Bool) (words : List (List Bool)) :
    wordInsertAllocation a words ≤ (wordInsertWithWork a words).2 := by
  induction words with
  | nil => rfl
  | cons b rest ih =>
    have hc := wordLEAllocation_le_work a b
    unfold wordInsertAllocation wordInsertWithWork
    dsimp only
    split_ifs <;> dsimp only
    · exact Nat.add_le_add_right hc 2
    · calc
        _ = (wordLEAllocation a b + wordInsertAllocation a rest) + 1 := (Nat.add_assoc _ _ _).symm
        _ ≤ _ := Nat.add_le_add (Nat.add_le_add hc ih) (by decide : 1 ≤ 2)



theorem wordSortAllocation_le_work (words : List (List Bool)) :
    wordSortAllocation words ≤ (wordSortWithWork words).2 := by
  induction words with
  | nil => simp only [wordSortAllocation, wordSortWithWork]; omega
  | cons a rest ih =>
    have hi := wordInsertAllocation_le_work a (wordSortWithWork rest).1
    simp only [wordSortAllocation, wordSortWithWork]
    omega

def wordLEInvocations (a b : List Bool) : ℕ := bitCompareInvocations b a + 1

theorem wordLEInvocations_le_work (a b : List Bool) :
    wordLEInvocations a b ≤ (wordLEWithWork a b).2 := by
  exact Nat.add_le_add_right (bitCompareInvocations_le_work b a) 1

def wordInsertInvocations (a : List Bool) : List (List Bool) → ℕ
  | [] => 1
  | b :: rest => wordLEInvocations a b +
    if (wordLEWithWork a b).1 then 1 else wordInsertInvocations a rest + 1

theorem wordInsertInvocations_le_work (a : List Bool) (words : List (List Bool)) :
    wordInsertInvocations a words ≤ (wordInsertWithWork a words).2 := by
  induction words with
  | nil => rfl
  | cons b rest ih =>
    have hc := wordLEInvocations_le_work a b
    unfold wordInsertInvocations wordInsertWithWork
    dsimp only
    split_ifs <;> dsimp only <;> omega

def wordSortInvocations : List (List Bool) → ℕ
  | [] => 1
  | a :: rest => wordSortInvocations rest +
    wordInsertInvocations a (wordSortWithWork rest).1 + 1

theorem wordSortInvocations_le_work (words : List (List Bool)) :
    wordSortInvocations words ≤ (wordSortWithWork words).2 := by
  induction words with
  | nil => simp only [wordSortInvocations, wordSortWithWork]; omega
  | cons a rest ih =>
    have hi := wordInsertInvocations_le_work a (wordSortWithWork rest).1
    simp only [wordSortInvocations, wordSortWithWork]
    omega

namespace BinaryFraction



theorem scaledCeilingAllocation_le_work (multiplier : ℕ) (a : BinaryFraction) :
    scaledCeilingAllocation multiplier a ≤ (scaledCeilingWithWork multiplier a).2 := by
  have hm := canonicalMulAllocation_le_work (nat multiplier) a
  have hc := naturalCeilingAllocation_le_work (canonicalMulWithWork (nat multiplier) a).1
  unfold scaledCeilingAllocation scaledCeilingWithWork
  dsimp only
  omega



theorem medianSeedAllocation_le_work (N multiplier : ℕ) (values : List BinaryFraction) :
    medianSeedAllocation N multiplier values ≤ (medianSeedWithWork N multiplier values).2 := by
  have hm := arithmeticMapAllocation_le_work (scaledCeilingWithWork multiplier)
    (scaledCeilingAllocation multiplier) values (fun a _ => scaledCeilingAllocation_le_work multiplier a)
  let rounded := (arithmeticMapWithWork (scaledCeilingWithWork multiplier) values).1
  have hs := wordSortAllocation_le_work rounded
  have hc := wordLEAllocation_le_work N.bits ((wordSortWithWork rounded).1.getD (values.length / 2) [])
  unfold medianSeedAllocation medianSeedWithWork wordMinWithWork
  dsimp only
  dsimp only [rounded] at hs hc
  omega



theorem seedMedianAllocation_le_work (N multiplier : ℕ) (values : List BinaryFraction) :
    seedMedianAllocation N multiplier values ≤ (seedMedianWithWork N multiplier values).2 := by
  have hm := medianSeedAllocation_le_work N multiplier values
  have ht := trimBitWordAllocation_le_work (medianSeedWithWork N multiplier values).1
  unfold seedMedianAllocation seedMedianWithWork
  dsimp only
  omega

def scaledCeilingInvocations (multiplier : ℕ) (a : BinaryFraction) : ℕ :=
  canonicalMulInvocations (nat multiplier) a +
    naturalCeilingInvocations (canonicalMulWithWork (nat multiplier) a).1 + 1

theorem scaledCeilingInvocations_le_work (multiplier : ℕ) (a : BinaryFraction) :
    scaledCeilingInvocations multiplier a ≤ (scaledCeilingWithWork multiplier a).2 := by
  have hm := canonicalMulInvocations_le_work (nat multiplier) a
  have hc := naturalCeilingInvocations_le_work (canonicalMulWithWork (nat multiplier) a).1
  unfold scaledCeilingInvocations scaledCeilingWithWork
  dsimp only
  omega

def medianSeedInvocations (N multiplier : ℕ) (values : List BinaryFraction) : ℕ :=
  let rounded := (arithmeticMapWithWork (scaledCeilingWithWork multiplier) values).1
  let sorted := (wordSortWithWork rounded).1
  arithmeticMapInvocations (scaledCeilingInvocations multiplier) values + wordSortInvocations rounded +
    wordLEInvocations N.bits (sorted.getD (values.length / 2) []) +
    values.length + 1

theorem medianSeedInvocations_le_work (N multiplier : ℕ) (values : List BinaryFraction) :
    medianSeedInvocations N multiplier values ≤ (medianSeedWithWork N multiplier values).2 := by
  have hm := arithmeticMapInvocations_le_work (scaledCeilingWithWork multiplier)
    (scaledCeilingInvocations multiplier) values (fun a _ => scaledCeilingInvocations_le_work multiplier a)
  let rounded := (arithmeticMapWithWork (scaledCeilingWithWork multiplier) values).1
  have hs := wordSortInvocations_le_work rounded
  have hc := wordLEInvocations_le_work N.bits ((wordSortWithWork rounded).1.getD (values.length / 2) [])
  unfold medianSeedInvocations medianSeedWithWork wordMinWithWork
  dsimp only
  dsimp only [rounded] at hs hc
  omega

def seedMedianInvocations (N multiplier : ℕ) (values : List BinaryFraction) : ℕ :=
  medianSeedInvocations N multiplier values +
    trimBitWordInvocations (medianSeedWithWork N multiplier values).1 + 1

theorem seedMedianInvocations_le_work (N multiplier : ℕ) (values : List BinaryFraction) :
    seedMedianInvocations N multiplier values ≤ (seedMedianWithWork N multiplier values).2 := by
  have hm := medianSeedInvocations_le_work N multiplier values
  have ht := trimBitWordInvocations_le_work (medianSeedWithWork N multiplier values).1
  unfold seedMedianInvocations seedMedianWithWork
  dsimp only
  omega

end BinaryFraction
end EditApproximation

end OAI
