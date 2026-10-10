import OAI.LinearAlgebra.MatrixMultiplication.Separation.ComplexFiniteControl

namespace OAI

/-! Tensor extraction over arbitrary fields and its asymptotic rate. -/

namespace MatrixMultiplication.AllFieldPopulationCounts

open scoped BigOperators

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]

def denominator (w : I → ℚ) : ℕ := ∏ i, (w i).den

def baseCount (w : I → ℚ) (i : I) : ℕ :=
  (w i).num.toNat * ∏ j ∈ Finset.univ.erase i, (w j).den

def count (w : I → ℚ) (m : ℕ) (i : I) : ℕ := m * baseCount w i

def blockLength (w : I → ℚ) (m : ℕ) : ℕ := m * denominator w

omit [DecidableEq I] in
theorem denominator_pos (w : I → ℚ) : 0 < denominator w := by
  exact Finset.prod_pos fun i _ => (w i).den_pos

theorem denominator_factor (w : I → ℚ) (i : I) :
    (w i).den * (∏ j ∈ Finset.univ.erase i, (w j).den) = denominator w := by
  exact Finset.mul_prod_erase Finset.univ (fun j => (w j).den) (Finset.mem_univ i)

theorem baseCount_cast (w : I → ℚ) (hw : ∀ i, 0 ≤ w i) (i : I) :
    (baseCount w i : ℚ) = (denominator w : ℚ) * w i := by
  have hnum : ((w i).num.toNat : ℚ) = ((w i).num : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.mpr (hw i))
  have hden : ((w i).den : ℚ) ≠ 0 := by exact_mod_cast (w i).den_ne_zero
  have hq : ((w i).num : ℚ) = w i * ((w i).den : ℚ) := by
    calc
      ((w i).num : ℚ) =
          (((w i).num : ℚ) / ((w i).den : ℚ)) * ((w i).den : ℚ) :=
        (div_mul_cancel₀ _ hden).symm
      _ = w i * ((w i).den : ℚ) := by rw [(w i).num_div_den]
  rw [baseCount, ← denominator_factor w i]
  push_cast
  rw [hnum, hq]
  ring

theorem count_cast (w : I → ℚ) (hw : ∀ i, 0 ≤ w i) (m : ℕ) (i : I) :
    (count w m i : ℚ) = (m : ℚ) * (denominator w : ℚ) * w i := by
  simp only [count, Nat.cast_mul, baseCount_cast w hw, mul_assoc]

theorem count_cast_blockLength (w : I → ℚ) (hw : ∀ i, 0 ≤ w i)
    (m : ℕ) (i : I) :
    (count w m i : ℚ) = (blockLength w m : ℚ) * w i := by
  simpa only [blockLength, Nat.cast_mul] using count_cast w hw m i

omit [DecidableEq I] in
theorem blockLength_pos (w : I → ℚ) {m : ℕ} (hm : 0 < m) :
    0 < blockLength w m := Nat.mul_pos hm (denominator_pos w)

theorem count_zero_iff (w : I → ℚ) (hw : ∀ i, 0 ≤ w i)
    {m : ℕ} (hm : 0 < m) (i : I) : count w m i = 0 ↔ w i = 0 := by
  have hD : (denominator w : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (denominator_pos w))
  have hM : (m : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hm)
  have h : (count w m i : ℚ) = 0 ↔ w i = 0 := by
    rw [count_cast w hw]
    simp only [mul_eq_zero, hM, hD, false_or]
  simpa only [Nat.cast_eq_zero] using h

theorem count_pos_iff (w : I → ℚ) (hw : ∀ i, 0 ≤ w i)
    {m : ℕ} (hm : 0 < m) (i : I) : 0 < count w m i ↔ 0 < w i := by
  rw [Nat.pos_iff_ne_zero, ne_eq, count_zero_iff w hw hm]
  constructor
  · intro h
    exact lt_of_le_of_ne (hw i) (Ne.symm h)
  · exact ne_of_gt

theorem sum_count_cast {J : Type*} (w : I → ℚ) (hw : ∀ i, 0 ≤ w i)
    (m : ℕ) (s : Finset J) (f : J → I) :
    ((∑ j ∈ s, count w m (f j) : ℕ) : ℚ) =
      (blockLength w m : ℚ) * ∑ j ∈ s, w (f j) := by
  simp only [Nat.cast_sum, count_cast_blockLength w hw]
  rw [Finset.mul_sum]

theorem transition_sum {J : Type*} (w : I → ℚ) (hw : ∀ i, 0 ≤ w i)
    (m : ℕ) (s : Finset J) (f : J → I) (parent : I)
    (hs : ∑ j ∈ s, w (f j) = w parent) :
    ∑ j ∈ s, count w m (f j) = count w m parent := by
  apply Nat.cast_injective (R := ℚ)
  rw [sum_count_cast w hw, hs, count_cast_blockLength w hw]

theorem unit_sum {J : Type*} (w : I → ℚ) (hw : ∀ i, 0 ≤ w i)
    (m : ℕ) (s : Finset J) (f : J → I)
    (hs : ∑ j ∈ s, w (f j) = 1) :
    ∑ j ∈ s, count w m (f j) = blockLength w m := by
  apply Nat.cast_injective (R := ℚ)
  rw [sum_count_cast w hw, hs, mul_one]

theorem count_eq_of_mass_eq (w : I → ℚ) (hw : ∀ i, 0 ≤ w i)
    (m : ℕ) {i j : I} (h : w i = w j) : count w m i = count w m j := by
  apply Nat.cast_injective (R := ℚ)
  rw [count_cast w hw, count_cast w hw, h]

theorem count_ratio (w : I → ℚ) (hw : ∀ i, 0 ≤ w i)
    {m : ℕ} (hm : 0 < m) (i : I) :
    (count w m i : ℚ) / blockLength w m = w i := by
  rw [count_cast_blockLength w hw]
  have h : (blockLength w m : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (blockLength_pos w hm))
  exact mul_div_cancel_left₀ _ h

theorem count_dilate (w : I → ℚ) (m n : ℕ) (i : I) :
    count w (m * n) i = m * count w n i := by simp [count, Nat.mul_assoc]

theorem dilation_le_count (w : I → ℚ) (hw : ∀ i, 0 ≤ w i)
    (m : ℕ) (i : I) (hi : 0 < w i) : m ≤ count w m i := by
  have hb : 0 < baseCount w i := by
    have h := (count_pos_iff w hw (m := 1) (by decide) i).2 hi
    simpa only [count, one_mul] using h
  calc
    m = m * 1 := (Nat.mul_one m).symm
    _ ≤ m * baseCount w i := Nat.mul_le_mul_left m hb

theorem two_le_positive_count (w : I → ℚ) (hw : ∀ i, 0 ≤ w i)
    {m : ℕ} (hm : 2 ≤ m) (i : I) (hi : 0 < w i) : 2 ≤ count w m i :=
  hm.trans (dilation_le_count w hw m i hi)

end

end MatrixMultiplication.AllFieldPopulationCounts

end OAI
