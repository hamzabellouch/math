import OAI.Geometry.RCD.Sobolev.SobolevPointedTestRecovery

namespace OAI

/-! # Rescaled energy of the actual recovered Dirichlet tests -/

open Set Metric Filter MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

omit [ProperSpace X] in
theorem NoncollapsedRCD.rescaled_test_energy_le {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) {p : X} {r S D : ℝ} (hr : 0<r) (hS : 0<S)
    (w : SobolevSpace (hausdorff n X) hX.quadratic) (L : ℝ≥0)
    (hL : r*(L:ℝ)≤D)
    (hgrad : ∀ᵐ x ∂hausdorff n X, SobolevSpace.minimalSlope (hausdorff n X) hX.quadratic w x≤L) :
    r^2*((hausdorff n X).real (ball p (S*r)))⁻¹*
      (∫ x in ball p (S*r), localGamma (hausdorff n X) hX.quadratic w w x ∂hausdorff n X)≤D^2 := by
  let μ := hausdorff n X
  let : IsFiniteMeasure (μ.restrict (ball p (S*r))) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using (hX.finiteOnBounded _ isBounded_ball)⟩
  have hmass : 0<μ.real (ball p (S*r)) :=
    ENNReal.toReal_pos (hX.fullSupport _ _ (mul_pos hS hr)).ne' (hX.finiteOnBounded _ isBounded_ball).ne
  have hb : ∀ᵐ x ∂μ.restrict (ball p (S*r)), localGamma μ hX.quadratic w w x≤(L:ℝ)^2 := by
    filter_upwards [ae_restrict_of_ae hgrad,ae_restrict_of_ae (localGamma_self μ hX.quadratic w),
      ae_restrict_of_ae ((Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ hX.quadratic w))]
      with x hx he hn
    rw [he]
    exact pow_le_pow_left₀ hn hx 2
  have hi := integral_mono_ae (localGamma_memL1 μ hX.quadratic w w).integrableOn
    (integrable_const ((L:ℝ)^2)) hb
  rw [integral_const,smul_eq_mul,Measure.real,Measure.restrict_apply_univ] at hi
  change (∫ x in ball p (S*r), localGamma μ hX.quadratic w w x ∂μ)≤
    μ.real (ball p (S*r))*(L:ℝ)^2 at hi
  have hnorm := mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr hmass.le)
  rw [← mul_assoc,inv_mul_cancel₀ hmass.ne',one_mul] at hnorm
  have hscaled := mul_le_mul_of_nonneg_left hnorm (sq_nonneg r)
  have hsq := pow_le_pow_left₀ (mul_nonneg hr.le L.coe_nonneg) hL 2
  have hsq' : r^2*(L:ℝ)^2≤D^2 := by simpa only [mul_pow] using hsq
  simpa only [mul_assoc] using hscaled.trans hsq'

end RegularPointCoordinates

end

end OAI
