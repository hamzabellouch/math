import Mathlib

namespace OAI

noncomputable section

open scoped InnerProductSpace BigOperators

namespace UniversalStrongKK

section Matrices

variable {ι κ H : Type*} [Fintype ι] [Fintype κ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

abbrev HilbertSum (ι H : Type*) [Fintype ι] [NormedAddCommGroup H] := PiLp 2 (fun _ : ι => H)

noncomputable def operatorMatrix (T : ι → κ → (H →L[ℂ] H)) :
    HilbertSum κ H →L[ℂ] HilbertSum ι H :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => ∑ j, (T i j).comp (PiLp.proj 2 (fun _ : κ => H) j)))

@[simp] theorem operatorMatrix_apply (T : ι → κ → (H →L[ℂ] H))
    (x : HilbertSum κ H) (i : ι) :
    (operatorMatrix T x).ofLp i = ∑ j, T i j (x.ofLp j) := by
  simp [operatorMatrix]

theorem operatorMatrix_add (S T : ι → κ → (H →L[ℂ] H)) :
    operatorMatrix (fun i j => S i j + T i j) = operatorMatrix S + operatorMatrix T := by
  ext x i
  simp [Finset.sum_add_distrib]

theorem operatorMatrix_smul (c : ℂ) (T : ι → κ → (H →L[ℂ] H)) :
    operatorMatrix (fun i j => c • T i j) = c • operatorMatrix T := by
  ext x i
  simp [Finset.smul_sum]

theorem operatorMatrix_mul {ν : Type*} [Fintype ν]
    (S : ι → κ → (H →L[ℂ] H)) (T : κ → ν → (H →L[ℂ] H)) :
    operatorMatrix (fun i k => ∑ j, S i j * T j k) =
      (operatorMatrix S).comp (operatorMatrix T) := by
  ext x i
  simp only [operatorMatrix_apply, sum_apply, mul_apply_eq_comp,
    ContinuousLinearMap.comp_apply, map_sum]
  exact Finset.sum_comm

variable [CompleteSpace H]

theorem operatorMatrix_star (T : ι → κ → (H →L[ℂ] H)) :
    operatorMatrix (fun i j => star (T j i)) = (operatorMatrix T).adjoint := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_right]
  simp only [PiLp.inner_apply, operatorMatrix_apply, inner_sum, sum_inner,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  exact Finset.sum_comm

end Matrices

end UniversalStrongKK

namespace UniversalStrongKK

section ProjectionMatrix

variable {ι κ H : Type*} [Fintype ι] [Fintype κ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem sum_pairwise_starProjection (p : ι → (H →L[ℂ] H))
    (hp : ∀ i, IsStarProjection (p i))
    (horth : ∀ i j, i ≠ j → p i * p j = 0) :
    IsStarProjection (∑ i, p i) := by
  classical
  constructor
  · change (∑ i, p i) * (∑ i, p i) = ∑ i, p i
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum, Finset.sum_eq_single i]
    · exact (hp i).isIdempotentElem.eq
    · intro j hj hji
      exact horth i j hji.symm
    · simp
  · change star (∑ i, p i) = ∑ i, p i
    simp only [star_sum, (hp _).isSelfAdjoint.star_eq]

omit [CompleteSpace H] in
theorem diagonalFamily_norm_le [DecidableEq κ] (p : κ → (H →L[ℂ] H)) (hp : ∀ j, ‖p j‖ ≤ 1) :
    ‖operatorMatrix (fun i j => if i = j then p i else 0)‖ ≤ 1 := by
  classical
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [one_mul]
  apply nonneg_le_nonneg_of_sq_le_sq (norm_nonneg _)
  rw [← sq, ← sq]
  simp_rw [← @inner_self_eq_norm_sq ℂ, PiLp.inner_apply, map_sum]
  apply Finset.sum_le_sum
  intro i hi
  have he : (operatorMatrix (fun i j => if i = j then p i else 0) x).ofLp i = p i (x.ofLp i) := by
    rw [operatorMatrix_apply, Finset.sum_eq_single i]
    · simp
    · intro j hj hji; simp [Ne.symm hji]
    · simp
  rw [he]
  simp only [inner_self_eq_norm_sq]
  have hn : ‖p i (x.ofLp i)‖ ≤ ‖x.ofLp i‖ := by
    calc
      _ ≤ ‖p i‖ * ‖x.ofLp i‖ := (p i).le_opNorm _
      _ ≤ 1 * ‖x.ofLp i‖ := mul_le_mul_of_nonneg_right (hp i) (norm_nonneg _)
      _ = _ := one_mul _
  exact pow_le_pow_left₀ (norm_nonneg _) hn 2

theorem orthogonal_projection_matrix_contraction (p : ι → κ → (H →L[ℂ] H))
    (hp : ∀ i j, IsStarProjection (p i j))
    (hrow : ∀ i j k, j ≠ k → p i j * p i k = 0)
    (hcol : ∀ i l j, i ≠ l → p i j * p l j = 0) :
    ‖operatorMatrix p‖ ≤ 1 := by
  classical
  let P (j : κ) := ∑ i, p i j
  have hP j : IsStarProjection (P j) :=
    sum_pairwise_starProjection (fun i => p i j) (fun i => hp i j) (fun i l h => hcol i l j h)
  have heq : (operatorMatrix p).adjoint.comp (operatorMatrix p) =
      operatorMatrix (fun j k => if j = k then P j else 0) := by
    rw [← operatorMatrix_star, ← operatorMatrix_mul]
    congr 1
    funext j k
    by_cases hjk : j = k
    · subst k
      simp only [ite_true, (hp _ _).isSelfAdjoint.star_eq, (hp _ _).isIdempotentElem.eq, P]
    · simp only [ite_eq_right hjk, (hp _ _).isSelfAdjoint.star_eq, hrow _ _ _ hjk,
        Finset.sum_const_zero]
  have hn := diagonalFamily_norm_le P (fun j => (hP j).norm_le (P j))
  rw [← heq, ContinuousLinearMap.norm_adjoint_comp_self] at hn
  nlinarith [norm_nonneg (operatorMatrix p)]

end ProjectionMatrix

end UniversalStrongKK
end

end OAI
