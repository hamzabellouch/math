import OAI.Analysis.KadisonKastler.SupportBounds

namespace OAI

/-!
# Matrices of orthogonal projections

The preservation-cut estimate uses an operator matrix whose nonzero
entries are projections, orthogonal within each row and each column.
Such a rectangular matrix is a contraction.
-/

namespace KadisonKastler

open Finset

noncomputable section

theorem isStarProjection_sum_orthogonal {A ι : Type*} [NonUnitalRing A] [StarRing A]
    (s : Finset ι) (P : ι → A) (hP : ∀ i ∈ s, IsStarProjection (P i))
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → P i * P j = 0) :
    IsStarProjection (∑ i ∈ s, P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [sum_insert hi]
    apply (hP i (by simp)).add
      (ih (by intro j hj; exact hP j (by simp [hj]))
        (by intro j hj k hk hjk; exact horth j (by simp [hj]) k (by simp [hk]) hjk))
    rw [mul_sum]
    apply sum_eq_zero
    intro j hj
    exact horth i (by simp) j (by simp [hj]) (by aesop)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem inner_eq_zero_of_selfAdjoint_mul_eq_zero
    (P Q : H →L[ℂ] H) (hP : IsSelfAdjoint P) (hPQ : P * Q = 0) (x y : H) :
    inner ℂ (P x) (Q y) = 0 := by
  have hstar : P.adjoint = P := hP.star_eq
  rw [← ContinuousLinearMap.adjoint_inner_right, hstar]
  have hz : P (Q y) = 0 := by
    change (P * Q) y = 0
    rw [hPQ]
    rfl
  rw [hz, inner_zero_right]

local instance projectionMatrixOrder : PartialOrder (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrder _
local instance projectionMatrixStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _

/-- Orthogonality in both directions makes a matrix of projections a
contraction, with no factor depending on the number of rows or columns. -/
theorem norm_projectionMatrix_le_one {I J : Type*} [Fintype I] [Fintype J]
    (T : CStarMatrix I J (H →L[ℂ] H))
    (hT : ∀ i j, IsStarProjection (T i j))
    (hrow : ∀ i j k, j ≠ k → T i j * T i k = 0)
    (hcol : ∀ j i k, i ≠ k → T i j * T k j = 0) : ‖T‖ ≤ 1 := by
  rw [← norm_rectangularHilbertMatrix]
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  rw [one_mul]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have hrows (i : I) : ‖∑ j, T i j (x j)‖ ^ 2 = ∑ j, ‖T i j (x j)‖ ^ 2 :=
    norm_sum_sq_of_pairwise_orthogonal univ _ (by
      intro j _ k _ hjk
      exact inner_eq_zero_of_selfAdjoint_mul_eq_zero _ _
        (hT i j).isSelfAdjoint (hrow i j k hjk) _ _)
  have hcols (j : J) : (∑ i, ‖T i j (x j)‖ ^ 2) ≤ ‖x j‖ ^ 2 := by
    have horth : ∀ i ∈ (univ : Finset I), ∀ k ∈ (univ : Finset I), i ≠ k →
        inner ℂ (T i j (x j)) (T k j (x j)) = 0 := by
      intro i _ k _ hik
      exact inner_eq_zero_of_selfAdjoint_mul_eq_zero _ _
        (hT i j).isSelfAdjoint (hcol j i k hik) _ _
    rw [← norm_sum_sq_of_pairwise_orthogonal univ _ horth, ← _root_.sum_apply]
    apply pow_le_pow_left₀ (norm_nonneg _)
    have hp : IsStarProjection (∑ i, T i j) :=
      isStarProjection_sum_orthogonal univ _ (fun i _ => hT i j)
        (fun i _ k _ hik => hcol j i k hik)
    calc
      _ ≤ ‖∑ i, T i j‖ * ‖x j‖ := (∑ i, T i j).le_opNorm _
      _ ≤ 1 * ‖x j‖ := mul_le_mul_of_nonneg_right
        (IsStarProjection.norm_le _ hp) (norm_nonneg _)
      _ = _ := one_mul _
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  simp_rw [rectangularHilbertMatrix_apply, hrows]
  rw [sum_comm]
  exact sum_le_sum (fun j _ => hcols j)

end

end KadisonKastler

end OAI
