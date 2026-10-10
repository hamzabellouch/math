import OAI.Combinatorics.ContingencyTables.Transport.IntegerWeightedTransport

namespace OAI

/-! # The integer transport recursion's future square identity

The three new--new removal entries partition by the same resulting pair.
Their coefficients give an exact nonnegative square, without a signature
assumption on the weighted future form.
-/

namespace ContingencyTables.IntegerWeightedTransport

open scoped BigOperators Classical Matrix
open CommonBasesFPRAS FactorialSignatures IntegerMarginal

lemma sum_range_shift (n s : ℕ) (f : ℕ → ℝ) :
    (∑ j ∈ Finset.range (n+s), if s ≤ j then f (j-s) else 0) =
      ∑ k ∈ Finset.range n, f k := by
  rw [Nat.add_comm n s, Finset.sum_range_add]
  have hz : (∑ j ∈ Finset.range s, if s ≤ j then f (j-s) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp [show ¬s ≤ j by have := Finset.mem_range.mp hj; omega]
  rw [hz, zero_add]
  apply Finset.sum_congr rfl
  intro j _
  simp

lemma sum_range_truncate (n s : ℕ) (f : ℕ → ℝ) :
    (∑ j ∈ Finset.range (n+s), if j < n then f j else 0) =
      ∑ k ∈ Finset.range n, f k := by
  rw [Finset.sum_range_add]
  have hz : (∑ j ∈ Finset.range s, if n+j < n then f (n+j) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    simp
  rw [hz, add_zero]
  apply Finset.sum_congr rfl
  intro j hj
  simp [Finset.mem_range.mp hj]

lemma sum_middle_shift (n : ℕ) (f : ℕ → ℝ) :
    (∑ j ∈ Finset.range (n+3), if 1 ≤ j ∧ j ≤ n+1 then f (j-1) else 0) =
      ∑ k ∈ Finset.range (n+1), f k := by
  rw [show n+3 = (n+2)+1 by omega, Finset.sum_range_succ]
  simp only [show ¬(1 ≤ n+2 ∧ n+2 ≤ n+1) by omega, ite_false, add_zero]
  convert sum_range_shift (n+1) 1 f using 1
  apply Finset.sum_congr rfl
  intro j hj
  have hjn := Finset.mem_range.mp hj
  simp [show j ≤ n+1 by omega]

variable {I : Type*} [Fintype I] [DecidableEq I]

omit [Fintype I] in
lemma future_aa (F : ((I ⊕ Bool) → ℕ) → ℝ) (z : I → ℕ) (n j : ℕ) :
    pairMatrix F (n+2) z j (.inr false) (.inr false) =
      if 2 ≤ j then F (profile z (j-2) (n+2-j)) else 0 := by
  have hv : ValidPair (profile z j (n+2-j)) (.inr false) (.inr false) ↔ 2 ≤ j := by
    simp [ValidPair, profile]; omega
  unfold IntegerMarginal.pairMatrix integerRemovalMatrix
  rw [if_congr hv rfl rfl, profile_removeAA]

omit [Fintype I] in
lemma future_bb (F : ((I ⊕ Bool) → ℕ) → ℝ) (z : I → ℕ) (n j : ℕ) :
    pairMatrix F (n+2) z j (.inr true) (.inr true) =
      if j ≤ n then F (profile z j (n-j)) else 0 := by
  have hv : ValidPair (profile z j (n+2-j)) (.inr true) (.inr true) ↔ j ≤ n := by
    simp [ValidPair, profile]; omega
  unfold IntegerMarginal.pairMatrix integerRemovalMatrix
  rw [if_congr hv rfl rfl, profile_removeBB]
  split_ifs <;> congr 1
  congr 1
  omega

omit [Fintype I] in
lemma future_ab (F : ((I ⊕ Bool) → ℕ) → ℝ) (z : I → ℕ) (n j : ℕ) :
    pairMatrix F (n+2) z j (.inr false) (.inr true) =
      if 1 ≤ j ∧ j ≤ n+1 then F (profile z (j-1) (n+1-j)) else 0 := by
  have hv : ValidPair (profile z j (n+2-j)) (.inr false) (.inr true) ↔
      1 ≤ j ∧ j ≤ n+1 := by
    simp [ValidPair, profile]; omega
  unfold IntegerMarginal.pairMatrix integerRemovalMatrix
  rw [if_congr hv rfl rfl, profile_removeAB]
  split_ifs <;> congr 1
  congr 1
  omega

omit [Fintype I] in
/-- The exact new--new part of the future correction: two diagonal
removals and the mixed removal of the same integer pair form a square. -/
theorem future_new_square
    (F : ((I ⊕ Bool) → ℕ) → ℝ) (z : I → ℕ) (n : ℕ) (g : ℕ → ℝ) :
    (∑ j ∈ Finset.range (n+3),
      (pairMatrix F (n+2) z j (.inr false) (.inr false) * g j ^ 2 -
      2 * pairMatrix F (n+2) z j (.inr false) (.inr true) * g j * g (j+1) +
      pairMatrix F (n+2) z j (.inr true) (.inr true) * g (j+1) ^ 2)) =
      ∑ k ∈ Finset.range (n+1), F (profile z k (n-k)) * (g (k+2)-g (k+1)) ^ 2 := by
  have haa : (∑ j ∈ Finset.range (n+3),
      pairMatrix F (n+2) z j (.inr false) (.inr false) * g j ^ 2) =
      ∑ k ∈ Finset.range (n+1), F (profile z k (n-k)) * g (k+2) ^ 2 := by
    convert sum_range_shift (n+1) 2 (fun k => F (profile z k (n-k)) * g (k+2)^2) using 1
    apply Finset.sum_congr rfl
    intro j _
    rw [future_aa]
    split_ifs with hj
    · rw [show j-2+2 = j by omega, show n-(j-2) = n+2-j by omega]
    · simp
  have hbb : (∑ j ∈ Finset.range (n+3),
      pairMatrix F (n+2) z j (.inr true) (.inr true) * g (j+1) ^ 2) =
      ∑ k ∈ Finset.range (n+1), F (profile z k (n-k)) * g (k+1) ^ 2 := by
    convert sum_range_truncate (n+1) 2 (fun k => F (profile z k (n-k)) * g (k+1)^2) using 1
    apply Finset.sum_congr rfl
    intro j _
    rw [future_bb]
    by_cases hj : j ≤ n
    · simp [hj, show j < n+1 by omega]
    · simp [hj, show ¬j < n+1 by omega]
  have hab : (∑ j ∈ Finset.range (n+3),
      2 * pairMatrix F (n+2) z j (.inr false) (.inr true) * g j * g (j+1)) =
      ∑ k ∈ Finset.range (n+1), 2 * F (profile z k (n-k)) * g (k+1) * g (k+2) := by
    convert sum_middle_shift n (fun k => 2 * F (profile z k (n-k)) * g (k+1) * g (k+2)) using 1
    apply Finset.sum_congr rfl
    intro j _
    rw [future_ab]
    split_ifs with hj
    · rw [show j-1+1 = j by omega, show j-1+2 = j+1 by omega,
        show n-(j-1) = n+1-j by omega]
    · simp
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, haa, hab, hbb,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

omit [Fintype I] in
/-- Every kernel entry has the same complete configuration; positivity
alone makes the future correction nonnegative. -/
theorem future_new_nonnegative
    (F : ((I ⊕ Bool) → ℕ) → ℝ) (z : I → ℕ) (n : ℕ) (g : ℕ → ℝ)
    (hF : ∀ p, 0 ≤ F p) :
    0 ≤ ∑ j ∈ Finset.range (n+3),
      (pairMatrix F (n+2) z j (.inr false) (.inr false) * g j ^ 2 -
      2 * pairMatrix F (n+2) z j (.inr false) (.inr true) * g j * g (j+1) +
      pairMatrix F (n+2) z j (.inr true) (.inr true) * g (j+1) ^ 2) := by
  rw [future_new_square]
  exact Finset.sum_nonneg (fun k _ => mul_nonneg (hF _) (sq_nonneg _))


/-- The two mixed old--new sums telescope, including both invalid
endpoint removals. -/
theorem future_mixed_cancel
    (F : ((I ⊕ Bool) → ℕ) → ℝ) (z : I → ℕ) (M : ℕ)
    (h : I → ℝ) (g : ℕ → ℝ) :
    (∑ j ∈ Finset.range (M+1),
      ((pairMatrix F M z j).toBilin' (old h) (Pi.single (.inr false) 1) * g j -
      (pairMatrix F M z j).toBilin' (old h) (Pi.single (.inr true) 1) * g (j+1))) = 0 := by
  calc
    _ = ∑ j ∈ Finset.range (M+1), (cross F M z j h * g j -
          cross F M z (j+1) h * g (j+1)) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjM : j ≤ M := by have := Finset.mem_range.mp hj; omega
      rw [cross_a F M z j hjM, cross_b F M z j hjM]
    _ = cross F M z 0 h * g 0 - cross F M z (M+1) h * g (M+1) :=
      Finset.sum_range_sub' (fun j => cross F M z j h * g j) (M+1)
    _ = 0 := by simp [cross]

/-- Old--old entries partition the parent's balanced marginal exactly. -/
theorem future_old_sum
    (F : ((I ⊕ Bool) → ℕ) → ℝ) (z : I → ℕ) (M : ℕ) (h : I → ℝ) :
    (∑ j ∈ Finset.range (M+1), (pairMatrix F M z j).toBilin' (old h) (old h)) =
      (integerRemovalMatrix (marginal F M) z).toBilin' h h := by
  rw [marginal_old_block]
  simp only [LinearMap.sum_apply, LinearMap.compl₁₂_apply]


noncomputable def extendCoefficients (h : I → ℝ) (a b : ℝ) : I ⊕ Bool → ℝ :=
  old h + a • Pi.single (.inr false) 1 - b • Pi.single (.inr true) 1


omit [Fintype I] in
@[simp] lemma extendCoefficients_inl (h : I → ℝ) (a b : ℝ) (i : I) :
    extendCoefficients h a b (.inl i) = h i := by
  simp [extendCoefficients, old]

omit [Fintype I] in
@[simp] lemma extendCoefficients_a (h : I → ℝ) (a b : ℝ) :
    extendCoefficients h a b (.inr false) = a := by
  simp [extendCoefficients, old]

omit [Fintype I] in
@[simp] lemma extendCoefficients_b (h : I → ℝ) (a b : ℝ) :
    extendCoefficients h a b (.inr true) = -b := by
  simp [extendCoefficients, old]

lemma extended_quadratic (B : Matrix (I ⊕ Bool) (I ⊕ Bool) ℝ)
    (hB : ∀ i j, B i j = B j i) (h : I → ℝ) (a b : ℝ) :
    B.toBilin' (extendCoefficients h a b) (extendCoefficients h a b) =
      B.toBilin' (old h) (old h) +
      2 * (B.toBilin' (old h) (Pi.single (.inr false) 1) * a -
        B.toBilin' (old h) (Pi.single (.inr true) 1) * b) +
      (B (.inr false) (.inr false) * a^2 -
        2 * B (.inr false) (.inr true) * a * b + B (.inr true) (.inr true) * b^2) := by
  have hs := matrix_bilin_symm B hB
  unfold extendCoefficients
  simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
    LinearMap.BilinForm.sub_left, LinearMap.BilinForm.sub_right,
    LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right]
  rw [hs.eq (Pi.single (.inr false) 1) (old h),
    hs.eq (Pi.single (.inr true) 1) (old h)]
  simp only [Matrix.toBilin'_single]
  rw [hB (.inr true) (.inr false)]
  ring

/-- Equation future-square of the first manuscript for actual integer
removal matrices. The parent is the balanced raw marginal. -/
theorem future_square_identity
    (F : ((I ⊕ Bool) → ℕ) → ℝ) (z : I → ℕ) (n : ℕ)
    (h : I → ℝ) (g : ℕ → ℝ) :
    (∑ j ∈ Finset.range (n+3),
      (pairMatrix F (n+2) z j).toBilin'
        (extendCoefficients h (g j) (g (j+1))) (extendCoefficients h (g j) (g (j+1)))) -
      (integerRemovalMatrix (marginal F (n+2)) z).toBilin' h h =
    ∑ k ∈ Finset.range (n+1), F (profile z k (n-k)) * (g (k+2)-g (k+1))^2 := by
  simp_rw [extended_quadratic (pairMatrix F (n+2) z _) (integerRemoval_symm F _) h]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    future_mixed_cancel, mul_zero, add_zero]
  rw [show n+3 = (n+2)+1 by omega, future_old_sum]
  rw [show n+2+1 = n+3 by omega, future_new_square]
  ring

/-- Processing an ordinary integer pair can only increase a future form.
No signature assertion about the weighted future kernel is required. -/
theorem future_form_monotone
    (F : ((I ⊕ Bool) → ℕ) → ℝ) (z : I → ℕ) (n : ℕ)
    (h : I → ℝ) (g : ℕ → ℝ) (hF : ∀ p, 0 ≤ F p) :
    (integerRemovalMatrix (marginal F (n+2)) z).toBilin' h h ≤
      ∑ j ∈ Finset.range (n+3), (pairMatrix F (n+2) z j).toBilin'
        (extendCoefficients h (g j) (g (j+1))) (extendCoefficients h (g j) (g (j+1))) := by
  apply sub_nonneg.mp
  rw [future_square_identity]
  exact Finset.sum_nonneg (fun k _ => mul_nonneg (hF _) (sq_nonneg _))

end ContingencyTables.IntegerWeightedTransport

end OAI
