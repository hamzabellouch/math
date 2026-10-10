import OAI.Analysis.BoundedHochschild.CompletelyBoundedFactorization

namespace OAI

/-! The operator in a factorization remains bounded under normalized row
averaging. Both represented rows are allowed to act on different Hilbert spaces. -/

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {I H K : Type*} [Fintype I]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma sum_norm_adjoint_sq (a : I → (H →L[ℂ] H))
    (ha : ∑ i, a i * star (a i) = 1) (ξ : H) :
    ∑ i, ‖(a i).adjoint ξ‖ ^ 2 = ‖ξ‖ ^ 2 := by
  have he : (∑ i, inner ℂ ((a i).adjoint ξ) ((a i).adjoint ξ)) = inner ℂ ξ ξ := by
    calc
      _ = ∑ i, inner ℂ ξ ((a i) ((a i).adjoint ξ)) := by
        apply Finset.sum_congr rfl
        intro i _
        exact (ContinuousLinearMap.adjoint_inner_left (a i) ((a i).adjoint ξ) ξ)
      _ = inner ℂ ξ ((∑ i, a i * star (a i)) ξ) := by
        simp only [sum_apply, inner_sum, ContinuousLinearMap.star_eq_adjoint]
        rfl
      _ = inner ℂ ξ ξ := by rw [ha]; rfl
  have hr := congrArg Complex.re he
  change Complex.re (∑ i, inner ℂ ((a i).adjoint ξ) ((a i).adjoint ξ)) =
    RCLike.re (inner ℂ ξ ξ) at hr
  simp only [Complex.re_sum] at hr
  change (∑ i, RCLike.re (inner ℂ ((a i).adjoint ξ) ((a i).adjoint ξ))) =
    RCLike.re (inner ℂ ξ ξ) at hr
  simpa only [inner_self_eq_norm_sq] using hr

omit [CompleteSpace K] in
lemma norm_sum_inner_sq_le (x y : I → K) :
    ‖∑ i, inner ℂ (x i) (y i)‖ ^ 2 ≤
      (∑ i, ‖x i‖ ^ 2) * ∑ i, ‖y i‖ ^ 2 := by
  have h : ‖∑ i, inner ℂ (x i) (y i)‖ ≤ ∑ i, ‖x i‖ * ‖y i‖ :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_inner_le_norm (x i) (y i))
  exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans
    (Finset.sum_mul_sq_le_sq_mul_sq _ _ _)

def operatorRowAverage (a : I → (K →L[ℂ] K)) (b : I → (H →L[ℂ] H))
    (W : H →L[ℂ] K) : H →L[ℂ] K :=
  ∑ i, (a i).comp (W.comp (b i).adjoint)

omit [CompleteSpace K] in
@[simp] lemma operatorRowAverage_apply (a : I → (K →L[ℂ] K))
    (b : I → (H →L[ℂ] H)) (W : H →L[ℂ] K) (ξ : H) :
    operatorRowAverage a b W ξ = ∑ i, a i (W ((b i).adjoint ξ)) := by
  simp only [operatorRowAverage, sum_apply, ContinuousLinearMap.comp_apply]

theorem operatorRowAverage_norm_le (a : I → (K →L[ℂ] K))
    (b : I → (H →L[ℂ] H)) (ha : ∑ i, a i * star (a i) = 1)
    (hb : ∑ i, b i * star (b i) = 1) (W : H →L[ℂ] K) :
    ‖operatorRowAverage a b W‖ ≤ ‖W‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg W)
  intro ξ
  let ζ := operatorRowAverage a b W ξ
  have he : inner ℂ ζ ζ = ∑ i, inner ℂ ((a i).adjoint ζ) (W ((b i).adjoint ξ)) := by
    conv_lhs => rhs; rw [show ζ = operatorRowAverage a b W ξ from rfl,
      operatorRowAverage_apply]
    rw [inner_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact (ContinuousLinearMap.adjoint_inner_left (a i) (W ((b i).adjoint ξ)) ζ).symm
  have hs : ∑ i, ‖W ((b i).adjoint ξ)‖ ^ 2 ≤ ‖W‖ ^ 2 * ‖ξ‖ ^ 2 := by
    calc
      _ ≤ ∑ i, (‖W‖ * ‖(b i).adjoint ξ‖) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        exact pow_le_pow_left₀ (norm_nonneg _) (W.le_opNorm _) 2
      _ = ‖W‖ ^ 2 * ∑ i, ‖(b i).adjoint ξ‖ ^ 2 := by
        simp only [mul_pow, Finset.mul_sum]
      _ = _ := by rw [sum_norm_adjoint_sq b hb ξ]
  have hi := norm_sum_inner_sq_le (fun i => (a i).adjoint ζ)
    (fun i => W ((b i).adjoint ξ))
  rw [← he, inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal,
    abs_of_nonneg (norm_nonneg ζ), sum_norm_adjoint_sq a ha ζ] at hi
  have hf : (‖ζ‖ ^ 2) ^ 2 ≤ ‖ζ‖ ^ 2 * (‖W‖ ^ 2 * ‖ξ‖ ^ 2) :=
    hi.trans (mul_le_mul_of_nonneg_left hs (sq_nonneg _))
  have hsq : ‖ζ‖ ^ 2 ≤ (‖W‖ * ‖ξ‖) ^ 2 := by nlinarith [sq_nonneg (‖ζ‖ ^ 2 - ‖W‖ ^ 2 * ‖ξ‖ ^ 2)]
  exact (sq_le_sq₀ (norm_nonneg ζ) (mul_nonneg (norm_nonneg W) (norm_nonneg ξ))).mp hsq

end BoundedHochschild.KadisonRingrose

end

end OAI
