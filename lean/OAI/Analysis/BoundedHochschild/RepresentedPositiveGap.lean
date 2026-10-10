import OAI.Analysis.BoundedHochschild.StrongRowDefect

namespace OAI

/-! The positive projection gap gives a uniform vector inequality in a
star representation. -/

noncomputable section

open scoped InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {M H : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma represented_positive_gap (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H))
    {p b : M} (hp : IsStarProjection p) {δ : ℝ} (hgap : δ • p ≤ star b * b)
    (ξ : H) : δ * ‖σ p ξ‖ ^ 2 ≤ ‖σ b (σ p ξ)‖ ^ 2 := by
  have hpos : 0 ≤ σ (star b * b - δ • p) := by
    simpa only [map_zero] using OrderHomClass.mono σ (sub_nonneg.mpr hgap)
  have h := (ContinuousLinearMap.nonneg_iff_isPositive.mp hpos).re_inner_nonneg_right (σ p ξ)
  have hsmul : σ (δ • p) = δ • σ p :=
    (σ.toLinearMap.restrictScalars ℝ).map_smul δ p
  have hpp : σ p (σ p ξ) = σ p ξ :=
    congrArg (fun A : H →L[ℂ] H => A ξ)
      ((map_mul σ p p).symm.trans (congrArg σ hp.isIdempotentElem.eq))
  rw [represented_norm_sq σ b (σ p ξ)]
  rw [map_sub, hsmul, sub_apply, smul_apply, hpp,
    inner_sub_right, inner_smul_right_eq_smul, map_sub, RCLike.smul_re, inner_self_eq_norm_sq] at h
  linarith

end BoundedHochschild.KadisonRingrose

end

end OAI
