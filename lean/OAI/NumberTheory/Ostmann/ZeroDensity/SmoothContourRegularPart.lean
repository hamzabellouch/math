import OAI.NumberTheory.Ostmann.ZeroDensity.SmoothContourResidue

namespace OAI

/-! # Removing each actual simple logarithmic-derivative pole

After adding back the zero's exact principal part, the smooth contour
integrand agrees locally with an analytic function.
-/

namespace Ostmann

open Filter
open scoped Topology

theorem smoothContour_regular_part (χ : PrimitiveComplexCharacter)
    (X : ℝ) (hX : 0 < X) (z : ℂ) :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R z ∧
      (fun s => (-deriv χ.L s / χ.L s) * smoothContourWeight X s +
        (analyticOrderNatAt χ.L z : ℂ) * smoothContourWeight X z / (s - z)) =ᶠ[𝓝[≠] z] R := by
  obtain ⟨g, hg, hgne, hsplit⟩ := χ.logDeriv_local_split z
  let W := smoothContourWeight X
  have hW : AnalyticAt ℂ W z := (smoothContourWeight_differentiable X hX).analyticAt z
  have hds : AnalyticAt ℂ (dslope W z) z := by
    obtain ⟨p, hp⟩ := hW
    exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩
  have hlog : AnalyticAt ℂ (logDeriv g) z := hg.deriv.div hg hgne
  let R : ℂ → ℂ := fun s => -(analyticOrderNatAt χ.L z : ℂ) * dslope W z s - logDeriv g s * W s
  refine ⟨R, (analyticAt_const.mul hds).sub (hlog.mul hW), ?_⟩
  filter_upwards [hsplit, self_mem_nhdsWithin] with s hs hsz
  have hneg : -deriv χ.L s / χ.L s = -logDeriv χ.L s := by
    rw [logDeriv_apply, neg_div]
  rw [hneg, hs]
  dsimp only [R]
  rw [dslope_of_ne W hsz]
  simp only [slope, smul_eq_mul]
  change -((analyticOrderNatAt χ.L z : ℂ) / (s - z) + logDeriv g s) * W s +
    (analyticOrderNatAt χ.L z : ℂ) * W z / (s - z) =
    -(analyticOrderNatAt χ.L z : ℂ) * ((s - z)⁻¹ * (W s - W z)) - logDeriv g s * W s
  ring

end Ostmann

end OAI
