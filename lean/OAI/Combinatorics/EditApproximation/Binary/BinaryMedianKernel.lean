import OAI.Combinatorics.EditApproximation.Binary.BinaryGroupKernel
import OAI.Combinatorics.EditApproximation.Binary.BinaryCeilingWork
import OAI.Combinatorics.EditApproximation.Probability.Median
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Binary multiplication, natural ceiling, sorting and clamping for the
literal seed median. The stored words are sorted without decoding them. -/

namespace EditApproximation

/-- Comparison of two stored nonnegative binary words. -/


@[simp] theorem wordLEWithWork_value (a b : List Bool) :
    (wordLEWithWork a b).1 = true ↔ bitWordValue a ≤ bitWordValue b := by
  simp only [wordLEWithWork, Bool.not_eq_true', decide_eq_false_iff_not,
    bitCompareWithWork_lt, not_lt]

theorem wordLEWithWork_cost (a b : List Bool) :
    (wordLEWithWork a b).2 ≤ 4 * (a.length + b.length) + 2 := by
  have h := bitCompareWithWork_cost b a
  change _ + 1 ≤ _
  omega



@[simp] theorem wordMinWithWork_value (a b : List Bool) :
    bitWordValue (wordMinWithWork a b).1 = min (bitWordValue a) (bitWordValue b) := by
  unfold wordMinWithWork
  dsimp only
  split_ifs with h
  · exact (min_eq_left ((wordLEWithWork_value a b).mp h)).symm
  · exact (min_eq_right (le_of_not_ge (fun hle => h ((wordLEWithWork_value a b).mpr hle)))).symm

theorem wordMinWithWork_length (a b : List Bool) :
    (wordMinWithWork a b).1.length ≤ max a.length b.length := by
  unfold wordMinWithWork
  dsimp only
  split_ifs <;> omega



@[simp] theorem wordInsertWithWork_value (a : List Bool) (words : List (List Bool)) :
    ((wordInsertWithWork a words).1.map bitWordValue) =
      List.orderedInsert (· ≤ ·) (bitWordValue a) (words.map bitWordValue) := by
  induction words with
  | nil => rfl
  | cons b rest ih =>
    unfold wordInsertWithWork
    dsimp only
    by_cases h : (wordLEWithWork a b).1 = true
    · have hle := (wordLEWithWork_value a b).mp h
      simp only [h, ↓reduceIte, List.map_cons, List.orderedInsert, hle]
    · have hle : ¬ bitWordValue a ≤ bitWordValue b := fun hle => h ((wordLEWithWork_value a b).mpr hle)
      simp only [h, Bool.false_eq_true, ↓reduceIte, List.map_cons, List.orderedInsert, hle, ih]

theorem wordInsertWithWork_length (a : List Bool) (words : List (List Bool)) :
    (wordInsertWithWork a words).1.length = words.length + 1 := by
  have h := congrArg List.length (wordInsertWithWork_value a words)
  simpa only [List.length_map, List.orderedInsert_length] using h

theorem wordInsertWithWork_words (a : List Bool) (words : List (List Bool)) (B : ℕ)
    (ha : a.length ≤ B) (hwords : ∀ b ∈ words, b.length ≤ B) :
    ∀ b ∈ (wordInsertWithWork a words).1, b.length ≤ B := by
  induction words with
  | nil =>
    intro b hb
    have heq : b = a := by simpa only [wordInsertWithWork, List.mem_singleton] using hb
    exact heq ▸ ha
  | cons b rest ih =>
    unfold wordInsertWithWork
    dsimp only
    split_ifs
    · intro c hc
      rcases List.mem_cons.mp hc with heq | hc
      · exact heq ▸ ha
      · exact hwords c hc
    · intro c hc
      rcases List.mem_cons.mp hc with heq | hc
      · exact heq ▸ hwords b (by simp)
      · exact ih (fun d hd => hwords d (by simp [hd])) c hc

theorem wordInsertWithWork_cost (a : List Bool) (words : List (List Bool)) (B : ℕ)
    (ha : a.length ≤ B) (hwords : ∀ b ∈ words, b.length ≤ B) :
    (wordInsertWithWork a words).2 ≤ (words.length + 1) * (8 * B + 4) := by
  induction words with
  | nil => simp only [wordInsertWithWork, List.length_nil, zero_add, one_mul]; omega
  | cons b rest ih =>
    have hb := hwords b (by simp)
    have hcmp := wordLEWithWork_cost a b
    have htail := ih (fun c hc => hwords c (by simp [hc]))
    unfold wordInsertWithWork
    dsimp only
    simp only [List.length_cons]
    rw [show rest.length + 1 + 1 = (rest.length + 1) + 1 by omega, Nat.add_mul, Nat.one_mul]
    split_ifs <;> omega



@[simp] theorem wordSortWithWork_value (words : List (List Bool)) :
    ((wordSortWithWork words).1.map bitWordValue) =
      List.insertionSort (· ≤ ·) (words.map bitWordValue) := by
  induction words with
  | nil => rfl
  | cons a rest ih =>
    simp only [wordSortWithWork, wordInsertWithWork_value, ih,
      List.map_cons, List.insertionSort_cons]

theorem wordSortWithWork_length (words : List (List Bool)) :
    (wordSortWithWork words).1.length = words.length := by
  have h := congrArg List.length (wordSortWithWork_value words)
  simpa only [List.length_map, List.length_insertionSort] using h

theorem wordSortWithWork_words (words : List (List Bool)) (B : ℕ)
    (hwords : ∀ b ∈ words, b.length ≤ B) :
    ∀ b ∈ (wordSortWithWork words).1, b.length ≤ B := by
  induction words with
  | nil => simp only [wordSortWithWork, List.not_mem_nil, false_implies, implies_true]
  | cons a rest ih =>
    exact wordInsertWithWork_words a (wordSortWithWork rest).1 B (hwords a (by simp))
      (ih (fun b hb => hwords b (by simp [hb])))

theorem wordSortWithWork_cost (words : List (List Bool)) (B : ℕ)
    (hwords : ∀ b ∈ words, b.length ≤ B) :
    (wordSortWithWork words).2 ≤ (words.length + 1) ^ 2 * (8 * B + 6) := by
  induction words with
  | nil => simp only [wordSortWithWork, List.length_nil, zero_add, one_pow, one_mul]; omega
  | cons a rest ih =>
    have hr : ∀ b ∈ rest, b.length ≤ B := fun b hb => hwords b (by simp [hb])
    have ht := ih hr
    have hi := wordInsertWithWork_cost a (wordSortWithWork rest).1 B (hwords a (by simp))
      (wordSortWithWork_words rest B hr)
    rw [wordSortWithWork_length] at hi
    change _ + _ + 2 ≤ _
    simp only [List.length_cons]
    nlinarith only [ht, hi, Nat.zero_le rest.length, Nat.zero_le B]

namespace BinaryFraction

theorem naturalCeilingWithWork_length (a : BinaryFraction) :
    (a.naturalCeilingWithWork).1.length ≤ a.width + 2 := by
  have hn : a.numerator.bits.length ≤ a.width := le_max_left _ _
  have h := bitCeilDivWithWork_length a.denominator a.numerator.bits
  unfold naturalCeilingWithWork
  split_ifs
  · change 0 ≤ a.width + 2
    omega
  · change (bitCeilDivWithWork a.denominator a.numerator.bits).1.length ≤ a.width + 2
    omega



@[simp] theorem scaledCeilingWithWork_value (multiplier : ℕ) (a : BinaryFraction) :
    bitWordValue (scaledCeilingWithWork multiplier a).1 = ⌈(multiplier : ℚ) * a.value⌉₊ := by
  simp only [scaledCeilingWithWork, naturalCeilingWithWork_value,
    canonicalMulWithWork_value, nat_value]

def scaledCeilingBitBudget (B : ℕ) : ℕ :=
  2000 * (B + 1) ^ 2 + 500 * (4 * B + 3) ^ 2 + B + 3

theorem scaledCeilingWithWork_bounds (multiplier : ℕ) (a : BinaryFraction) (B : ℕ)
    (hm : Nat.size multiplier + 2 ≤ B) (ha : a.width ≤ B) :
    (scaledCeilingWithWork multiplier a).1.length ≤ 4 * B + 4 ∧
      (scaledCeilingWithWork multiplier a).2 ≤ scaledCeilingBitBudget B := by
  have hm' : (nat multiplier).width ≤ B := (nat_width_le _).trans hm
  have hpw := canonicalMulWithWork_width (nat multiplier) a B hm' ha
  have hpc := canonicalMulWithWork_cost (nat multiplier) a B hm' ha
  have hcw := naturalCeilingWithWork_length (canonicalMulWithWork (nat multiplier) a).1
  have hcc := naturalCeilingWithWork_cost (canonicalMulWithWork (nat multiplier) a).1
  have hs := Nat.pow_le_pow_left (show (canonicalMulWithWork (nat multiplier) a).1.width + 1 ≤
      4 * B + 3 by omega) 2
  constructor
  · change (naturalCeilingWithWork (canonicalMulWithWork (nat multiplier) a).1).1.length ≤ _
    omega
  · change _ + _ + _ + 3 ≤ _
    unfold scaledCeilingBitBudget
    omega

/-- The exact clamped upper median on binary words, including every copy's
multiplication and ceiling, all sorting comparisons and the middle read. -/


@[simp] theorem medianSeedWithWork_value (N multiplier : ℕ) (values : List BinaryFraction) :
    bitWordValue (medianSeedWithWork N multiplier values).1 =
      min N (upperMedian (values.map fun a => ⌈(multiplier : ℚ) * a.value⌉₊)) := by
  unfold medianSeedWithWork
  rw [wordMinWithWork_value, bitWordValue_bits]
  congr 1
  rw [upperMedian, List.length_map, List.mergeSort_eq_insertionSort]
  have hs := wordSortWithWork_value
    (arithmeticMapWithWork (scaledCeilingWithWork multiplier) values).1
  rw [arithmeticMapWithWork_value, List.map_map] at hs
  simp only [Function.comp_def, scaledCeilingWithWork_value] at hs
  have hm := congrArg (fun words : List ℕ => words.getD (values.length / 2) 0) hs
  change ((wordSortWithWork (values.map (fun a => (scaledCeilingWithWork multiplier a).1))).1.map
    bitWordValue).getD (values.length / 2) (bitWordValue []) = _ at hm
  rw [List.getD_map] at hm
  simpa only [arithmeticMapWithWork_value] using hm

def medianSeedBitBudget (n B : ℕ) : ℕ :=
  n * (scaledCeilingBitBudget B + 3) + (n + 1) ^ 2 * (8 * (4 * B + 4) + 6) +
    n + 4 * (B + (4 * B + 4)) + 3 + B + 3

theorem medianSeedWithWork_bounds (N multiplier : ℕ) (values : List BinaryFraction) (B : ℕ)
    (hN : Nat.size N ≤ B) (hm : Nat.size multiplier + 2 ≤ B)
    (hv : ∀ a ∈ values, a.width ≤ B) :
    (medianSeedWithWork N multiplier values).1.length ≤ 4 * B + 4 ∧
      (medianSeedWithWork N multiplier values).2 ≤ medianSeedBitBudget values.length B := by
  let rounded := arithmeticMapWithWork (scaledCeilingWithWork multiplier) values
  have hlen : rounded.1.length = values.length := by
    simp only [rounded, arithmeticMapWithWork_value, List.length_map]
  have hrounded : ∀ word ∈ rounded.1, word.length ≤ 4 * B + 4 := by
    intro word hword
    simp only [rounded, arithmeticMapWithWork_value] at hword
    obtain ⟨a, ha, heq⟩ := List.mem_map.mp hword
    subst word
    exact (scaledCeilingWithWork_bounds multiplier a B hm (hv a ha)).1
  have hmc := arithmeticMapWithWork_cost (scaledCeilingWithWork multiplier) values
    (scaledCeilingBitBudget B) (fun a ha => (scaledCeilingWithWork_bounds multiplier a B hm (hv a ha)).2)
  have hsort := wordSortWithWork_cost rounded.1 (4 * B + 4) hrounded
  rw [hlen] at hsort
  let middle := (wordSortWithWork rounded.1).1.getD (values.length / 2) []
  have hmid : middle.length ≤ 4 * B + 4 := by
    by_cases hi : values.length / 2 < (wordSortWithWork rounded.1).1.length
    · dsimp only [middle]
      rw [List.getD_eq_getElem _ _ hi]
      exact wordSortWithWork_words rounded.1 (4 * B + 4) hrounded _ (List.getElem_mem hi)
    · simp only [middle, List.getD_eq_default _ _ (Nat.le_of_not_gt hi), List.length_nil]
      omega
  have hc := wordLEWithWork_cost N.bits middle
  have hn : N.bits.length ≤ B := by simpa only [← Nat.size_eq_bits_len] using hN
  have hl := wordMinWithWork_length N.bits middle
  constructor
  · change (wordMinWithWork N.bits middle).1.length ≤ _
    omega
  · change rounded.2 + (wordSortWithWork rounded.1).2 + values.length +
      ((wordLEWithWork N.bits middle).2 + 1) + Nat.size N + 3 ≤ _
    unfold medianSeedBitBudget
    change rounded.2 ≤ _ at hmc
    omega

end BinaryFraction
end EditApproximation

end OAI
