import OAI.Combinatorics.ContingencyTables.Transport.IntegerFutureSquare

namespace OAI

/-!
# The weighted future-slot kernel

Weights a(M-a) are used inside the finite box 0≤a≤M. The common
nonnegative kernel identifies the integer transport's future correction
matrix.
-/

namespace ContingencyTables.IntegerWeightedTransport

open scoped BigOperators Classical Matrix
open CommonBasesFPRAS FactorialSignatures IntegerMarginal

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def weightedFuture (F : ((I ⊕ Bool) → ℕ) → ℝ) (M : ℕ) (z : I → ℕ) : ℝ :=
  ∑ a ∈ Finset.range (M+1), (a:ℝ)*((M:ℝ)-a)*F (profile z a (M-a))

omit [Fintype I] [DecidableEq I] in
lemma weightedFuture_nonnegative (F : ((I ⊕ Bool) → ℕ) → ℝ) (M : ℕ)
    (hF : ∀ p, 0 ≤ F p) (z : I → ℕ) : 0 ≤ weightedFuture F M z := by
  apply Finset.sum_nonneg
  intro a ha
  have haM : a ≤ M := by have := Finset.mem_range.mp ha; omega
  have haR : (a:ℝ) ≤ M := by exact_mod_cast haM
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr haR)) (hF _)

omit [Fintype I] in
/-- Weighted future matrices are the old block of the literal common
kernel. This is an equality, with no one-positive-direction hypothesis. -/
theorem weightedFuture_matrix (F : ((I ⊕ Bool) → ℕ) → ℝ) (M : ℕ) (z : I → ℕ) :
    integerRemovalMatrix (weightedFuture F M) z =
      ∑ a ∈ Finset.range (M+1), ((a:ℝ)*((M:ℝ)-a)) •
        (pairMatrix F M z a).submatrix Sum.inl Sum.inl := by
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.submatrix_apply, pairMatrix_old, integerRemovalMatrix, weightedFuture]
  split_ifs <;> simp

/-- The scalar correction Q_t is exactly the weighted two-old-hole sum. -/
theorem weightedFuture_form (F : ((I ⊕ Bool) → ℕ) → ℝ) (M : ℕ)
    (z : I → ℕ) (h : I → ℝ) :
    (integerRemovalMatrix (weightedFuture F M) z).toBilin' h h =
      ∑ a ∈ Finset.range (M+1), (a:ℝ)*((M:ℝ)-a)*
        (pairMatrix F M z a).toBilin' (old h) (old h) := by
  rw [weightedFuture_matrix]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [old_old]

/-- Applying the square identity to the manuscript's weighted future
kernel proves monotonicity for that kernel itself. -/
theorem weighted_future_monotone
    (F : (((I ⊕ Bool) ⊕ Bool) → ℕ) → ℝ) (M : ℕ) (z : I → ℕ) (n : ℕ)
    (h : I → ℝ) (g : ℕ → ℝ) (hF : ∀ p, 0 ≤ F p) :
    (integerRemovalMatrix (marginal (weightedFuture F M) (n+2)) z).toBilin' h h ≤
      ∑ j ∈ Finset.range (n+3), (pairMatrix (weightedFuture F M) (n+2) z j).toBilin'
        (extendCoefficients h (g j) (g (j+1))) (extendCoefficients h (g j) (g (j+1))) :=
  future_form_monotone (weightedFuture F M) z n h g (weightedFuture_nonnegative F M hF)

/-- Exchange the current and future pairs, leaving all old coordinates
fixed. This makes the common summation domain explicit. -/
def swapPairs : ((I ⊕ Bool) ⊕ Bool) ≃ ((I ⊕ Bool) ⊕ Bool) where
  toFun
    | .inl (.inl i) => .inl (.inl i)
    | .inl (.inr b) => .inr b
    | .inr b => .inl (.inr b)
  invFun
    | .inl (.inl i) => .inl (.inl i)
    | .inl (.inr b) => .inr b
    | .inr b => .inl (.inr b)
  left_inv x := by rcases x with (i | b) | b <;> rfl
  right_inv x := by rcases x with (i | b) | b <;> rfl

omit [Fintype I] [DecidableEq I] in
lemma profile_swap (z : I → ℕ) (j k a b : ℕ) :
    (fun t => profile (profile z a b) j k (swapPairs t)) =
      profile (profile z j k) a b := by
  funext t
  rcases t with (i | c) | c <;> rfl

omit [Fintype I] [DecidableEq I] in
/-- The weighted future sum and the current balanced sum commute on
one fixed set of complete configurations. -/
theorem weightedFuture_marginal_commute
    (F : (((I ⊕ Bool) ⊕ Bool) → ℕ) → ℝ) (U M : ℕ) (z : I → ℕ) :
    marginal (weightedFuture F M) U z =
      weightedFuture (marginal (fun v => F (fun t => v (swapPairs t))) U) M z := by
  unfold marginal weightedFuture
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  dsimp only
  rw [profile_swap]

end ContingencyTables.IntegerWeightedTransport

end OAI
