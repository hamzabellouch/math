import OAI.Analysis.BoundedHochschild.OperatorRowAverages

namespace OAI

/-! Vector estimates for rows whose positive square sum is at most one.
These estimates control tails when a normalized row has infinitely many entries. -/

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {I H K : Type*} [Fintype I]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma sum_norm_adjoint_sq_le (a : I → (H →L[ℂ] H))
    (ha : ∑ i, a i * star (a i) ≤ 1) (ξ : H) :
    ∑ i, ‖(a i).adjoint ξ‖ ^ 2 ≤ ‖ξ‖ ^ 2 := by
  have hp := (ContinuousLinearMap.nonneg_iff_isPositive.mp (sub_nonneg.mpr ha)).re_inner_nonneg_right ξ
  have he : (∑ i, inner ℂ ((a i).adjoint ξ) ((a i).adjoint ξ)) =
      inner ℂ ξ ((∑ i, a i * star (a i)) ξ) := by
    rw [sum_apply, inner_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact ContinuousLinearMap.adjoint_inner_left (a i) ((a i).adjoint ξ) ξ
  have hr := congrArg Complex.re he
  change Complex.re (∑ i, inner ℂ ((a i).adjoint ξ) ((a i).adjoint ξ)) = _ at hr
  simp only [Complex.re_sum] at hr
  change (∑ i, RCLike.re (inner ℂ ((a i).adjoint ξ) ((a i).adjoint ξ))) = _ at hr
  simp only [inner_self_eq_norm_sq] at hr
  simp only [sub_apply, one_apply_eq_self, inner_sub_right, map_sub,
    inner_self_eq_norm_sq] at hp
  change 0 ≤ ‖ξ‖ ^ 2 - Complex.re (inner ℂ ξ ((∑ i, a i * star (a i)) ξ)) at hp
  linarith

lemma norm_sum_row_apply_sq_le (a : I → (K →L[ℂ] K))
    (ha : ∑ i, a i * star (a i) ≤ 1) (y : I → K) :
    ‖∑ i, a i (y i)‖ ^ 2 ≤ ∑ i, ‖y i‖ ^ 2 := by
  let ζ := ∑ i, a i (y i)
  have he : inner ℂ ζ ζ = ∑ i, inner ℂ ((a i).adjoint ζ) (y i) := by
    conv_lhs => rhs; rw [show ζ = ∑ i, a i (y i) from rfl]
    rw [inner_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact (ContinuousLinearMap.adjoint_inner_left (a i) (y i) ζ).symm
  have hi := norm_sum_inner_sq_le (fun i => (a i).adjoint ζ) y
  rw [← he, inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal,
    abs_of_nonneg (norm_nonneg ζ)] at hi
  have hs := sum_norm_adjoint_sq_le a ha ζ
  have hnonneg : 0 ≤ ∑ i, ‖y i‖ ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hf : (‖ζ‖ ^ 2) ^ 2 ≤ ‖ζ‖ ^ 2 * ∑ i, ‖y i‖ ^ 2 :=
    hi.trans (mul_le_mul_of_nonneg_right hs hnonneg)
  change ‖ζ‖ ^ 2 ≤ _
  nlinarith [sq_nonneg (‖ζ‖ ^ 2 - ∑ i, ‖y i‖ ^ 2)]

lemma operatorRowAverage_apply_sq_le (a : I → (K →L[ℂ] K))
    (b : I → (H →L[ℂ] H)) (ha : ∑ i, a i * star (a i) ≤ 1)
    (W : H →L[ℂ] K) (ξ : H) :
    ‖operatorRowAverage a b W ξ‖ ^ 2 ≤
      ‖W‖ ^ 2 * ∑ i, ‖(b i).adjoint ξ‖ ^ 2 := by
  rw [operatorRowAverage_apply]
  refine (norm_sum_row_apply_sq_le a ha _).trans ?_
  calc
    _ ≤ ∑ i, (‖W‖ * ‖(b i).adjoint ξ‖) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact pow_le_pow_left₀ (norm_nonneg _) (W.le_opNorm _) 2
    _ = _ := by simp only [mul_pow, Finset.mul_sum]

lemma operatorRowAverage_norm_le_of_le (a : I → (K →L[ℂ] K))
    (b : I → (H →L[ℂ] H)) (ha : ∑ i, a i * star (a i) ≤ 1)
    (hb : ∑ i, b i * star (b i) ≤ 1) (W : H →L[ℂ] K) :
    ‖operatorRowAverage a b W‖ ≤ ‖W‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg W)
  intro ξ
  have h := (operatorRowAverage_apply_sq_le a b ha W ξ).trans
    (mul_le_mul_of_nonneg_left (sum_norm_adjoint_sq_le b hb ξ) (sq_nonneg ‖W‖))
  rw [← mul_pow] at h
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg W) (norm_nonneg ξ))).mp h

end BoundedHochschild.KadisonRingrose

end

end OAI
