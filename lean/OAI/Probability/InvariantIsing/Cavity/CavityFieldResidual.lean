import OAI.Probability.InvariantIsing.Cavity.CavityFieldPath

namespace OAI

/-! The terminal ordinary residual covariance is the remaining tail of
the field-density integral; it is not an additional cascade level. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators Topology

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

lemma deficit_eq_one_sub_of_ae_le (p : OverlapPath) {r : ℝ}
    (hr : ∀ᵐ s ∂pathMeasure, p s ≤ r) : deficit p r = 1 - r := by
  have he : (fun s => max (p s - r) 0) =ᵐ[pathMeasure] (fun _ => 0) :=
    hr.mono (fun _ hs => max_eq_right (sub_nonpos.mpr hs))
  rw [deficit, integral_congr_ae he, integral_zero, sub_zero]

theorem integral_cavityFieldDensity_tail (rho lam : ι → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (p : OverlapPath) {top : ℝ} (htop : top ≤ 1)
    (hbound : ∀ᵐ s ∂pathMeasure, p s ≤ top) :
    (∫ r in top..1, cavityFieldDensity rho lam hrho hsum p r) =
      finiteR rho lam hrho hsum (deficit p top) - finiteR rho lam hrho hsum 0 := by
  let R := finiteR rho lam hrho hsum
  have he (r : ℝ) (hr : r ∈ Icc top 1) : deficit p r = 1 - r :=
    deficit_eq_one_sub_of_ae_le p (hbound.mono (fun _ hs => hs.trans hr.1))
  have hi : Continuous (fun r : ℝ => cavityRDerivative rho lam hrho hsum (1 - r)) :=
    (continuous_cavityRDerivative rho lam hrho hsum).comp
      (continuous_const.sub continuous_id)
  have hd : ∀ r ∈ Ioo top 1, HasDerivAt (fun r => R (1 - r))
      (-cavityRDerivative rho lam hrho hsum (1 - r)) r := by
    intro r hr
    have hp : 0 < 1 - r := sub_pos.mpr hr.2
    have hR := (hasStrictDerivAt_finiteR rho lam hrho hsum hp).hasDerivAt
    rw [← hR.deriv, ← cavityRDerivative_eq_deriv rho lam hrho hsum hp] at hR
    convert! hR.comp r ((hasDerivAt_id r).const_sub 1) using 1
    ring
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le htop
    (((continuous_finiteR rho lam hrho hsum).comp
      (continuous_const.sub continuous_id)).continuousOn) hd
    ((hi.intervalIntegrable top 1).neg)
  rw [intervalIntegral.integral_neg] at hf
  have hreplace : (∫ r in top..1, cavityFieldDensity rho lam hrho hsum p r) =
      ∫ r in top..1, cavityRDerivative rho lam hrho hsum (1 - r) := by
    apply intervalIntegral.integral_congr_Ioo_of_le htop
    intro r hr
    change cavityRDerivative rho lam hrho hsum (deficit p r) = _
    rw [he r ⟨hr.1.le, hr.2.le⟩]
  rw [hreplace, deficit_eq_one_sub_of_ae_le p hbound]
  simp only [Function.comp_apply, Pi.sub_apply, id_eq, sub_self] at hf
  linarith

theorem cavityField_residual (rho lam : ι → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (p : OverlapPath) {top : ℝ} (htop : top ≤ 1)
    (hbound : ∀ᵐ s ∂pathMeasure, p s ≤ top) :
    cavityFieldDiagonal rho lam hrho hsum p - cavityFieldPrimitive rho lam hrho hsum p top =
      finiteR rho lam hrho hsum (deficit p top) - finiteR rho lam hrho hsum 0 := by
  rw [cavityFieldDiagonal, cavityFieldPrimitive_sub]
  exact integral_cavityFieldDensity_tail rho lam hrho hsum p htop hbound

end InvariantIsing

end

end OAI
