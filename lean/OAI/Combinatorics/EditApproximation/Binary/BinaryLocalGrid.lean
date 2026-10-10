import OAI.Combinatorics.EditApproximation.Binary.BinaryRoundedKernel
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Local endpoint lists executed with binary division, multiplication,
subtraction and validity comparisons. Only the bounded grid-index range
is visited. -/

namespace EditApproximation



@[simp] theorem saturatingSubtractWithWork_value (a b : ℕ) :
    bitWordValue (saturatingSubtractWithWork a b).1 = a - b := by
  unfold saturatingSubtractWithWork
  dsimp only
  split_ifs with h
  · have hlt := (binaryNaturalCompareWithWork_lt a b).mp h
    simp only [bitWordValue, Nat.sub_eq_zero_of_le hlt.le]
  · exact binaryNaturalSubtractWithWork_value a b (le_of_not_gt (fun hab =>
      h ((binaryNaturalCompareWithWork_lt a b).mpr hab)))

theorem saturatingSubtractWithWork_cost (a b : ℕ) :
    (saturatingSubtractWithWork a b).2 ≤ 13 * (Nat.size a + Nat.size b) + 4 := by
  have htest := binaryNaturalCompareWithWork_cost a b
  have hsub := binaryNaturalSubtractWithWork_cost a b
  unfold saturatingSubtractWithWork
  dsimp only
  split_ifs <;> omega

theorem naturalCeiling_div_eq_ceilDiv (lo g : ℕ) (hg : 0 < g) :
    ⌈(lo : ℚ) / g⌉₊ = lo ⌈/⌉ g := by
  have hgQ : (0 : ℚ) < g := by exact_mod_cast hg
  apply Nat.le_antisymm
  · apply Nat.ceil_le.mpr
    apply (div_le_iff₀ hgQ).mpr
    have h := (ceilDiv_le_iff_le_mul hg).mp (le_rfl : lo ⌈/⌉ g ≤ lo ⌈/⌉ g)
    exact_mod_cast (by simpa only [mul_comm] using h : lo ≤ (lo ⌈/⌉ g) * g)
  · apply (ceilDiv_le_iff_le_mul hg).mpr
    have h := (div_le_iff₀ hgQ).mp (Nat.le_ceil ((lo : ℚ) / g))
    exact_mod_cast (by simpa only [mul_comm] using h : (lo : ℚ) ≤ g * ⌈(lo : ℚ) / g⌉₊)



@[simp] theorem gridPointsWithWork_value (g lo hi : ℕ) (hg : 0 < g) :
    (gridPointsWithWork g lo hi).1 = gridPointsBetween g lo hi := by
  have hl : bitWordValue (bitCeilDivWithWork g.bits lo.bits).1 = lo ⌈/⌉ g := by
    rw [bitCeilDivWithWork_value _ _ (by simpa only [bitWordValue_bits] using hg),
      bitWordValue_bits, bitWordValue_bits, naturalCeiling_div_eq_ceilDiv lo g hg]
  have hu := (binaryNaturalDivModWithWork_spec hi g hg).1
  simp only [gridPointsWithWork, arithmeticMapWithWork_value, binaryNaturalMulWithWork_value,
    saturatingSubtractWithWork_value, binaryNaturalAddWithWork_value, hl, hu, gridPointsBetween]



@[simp] theorem makeStateWithWork_value (n lo hi : ℕ) :
    (makeStateWithWork n lo hi).1 = makeTargetState n lo hi := by
  have htest : ((wordLEWithWork lo.bits hi.bits).1 && (wordLEWithWork hi.bits n.bits).1) = true ↔
      lo ≤ hi ∧ hi ≤ n := by
    simp only [Bool.and_eq_true, wordLEWithWork_value, bitWordValue_bits]
  unfold makeStateWithWork makeTargetState
  dsimp only
  by_cases h : lo ≤ hi ∧ hi ≤ n
  · rw [dite_eq_left (htest.mpr h), dite_eq_left h]
  · rw [dite_eq_right (fun ht => h (htest.mp ht)), dite_eq_right h]



@[simp] theorem filterMapWithWork_value {α β : Type*} (f : α → Option β × ℕ) (values : List α) :
    (filterMapWithWork f values).1 = values.filterMap (fun a => (f a).1) := by
  induction values with
  | nil => rfl
  | cons a rest ih =>
    simp only [filterMapWithWork, List.filterMap_cons, ih]
    cases (f a).1 <;> rfl

theorem filterMapWithWork_cost {α β : Type*} (f : α → Option β × ℕ) (values : List α)
    (C : ℕ) (hC : ∀ a ∈ values, (f a).2 ≤ C) :
    (filterMapWithWork f values).2 ≤ values.length * (C + 3) := by
  induction values with
  | nil => simp only [filterMapWithWork, List.length_nil, Nat.zero_mul, le_refl]
  | cons a rest ih =>
    have ha := hC a (by simp)
    have ht := ih (fun b hb => hC b (by simp [hb]))
    change (f a).2 + (filterMapWithWork f rest).2 + 3 ≤ _
    simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
    omega



@[simp] theorem gridStateBoxWithWork_value (n g radius lo hi : ℕ) (hg : 0 < g) :
    (gridStateBoxWithWork n g radius lo hi).1 = gridStateBox n g radius lo hi := by
  simp only [gridStateBoxWithWork, arithmeticFlatMapWithWork_value, filterMapWithWork_value,
    makeStateWithWork_value, gridPointsWithWork_value _ _ _ hg, saturatingSubtractWithWork_value,
    binaryNaturalAddWithWork_value, gridStateBox]

end EditApproximation

end OAI
