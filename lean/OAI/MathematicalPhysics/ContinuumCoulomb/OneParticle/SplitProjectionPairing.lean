import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.SplitFrameBound

namespace OAI

/-! Fubini identities for the actual localized tensor orbitals and the
transverse residual. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem planarCoefficient_pair_tensor {freq : ℝ} (hfreq : 0 < freq)
    (u : PlanarPosition) (f : SplitPosition → ℝ) (hf : MemLp f 2) :
    (∫ z, planarCoefficient u f z*verticalMode freq z) =
      ∫ p, f p*localizedMode freq u p := by
  have hi : Integrable (fun p => f p*localizedMode freq u p)
      ((volume : Measure PlanarPosition).prod (volume : Measure ℝ)) := by
    rw [← Measure.volume_eq_prod]
    exact hf.integrable_mul (localizedMode_memLp hfreq u)
  rw [Measure.volume_eq_prod,integral_prod_symm _ hi]
  apply integral_congr_ae
  filter_upwards [] with z
  unfold planarCoefficient
  rw [← integral_mul_const]
  apply integral_congr_ae
  filter_upwards [] with r
  unfold localizedMode
  ring

theorem verticalCoefficient_pair_tensor {freq : ℝ} (hfreq : 0 < freq)
    (u : PlanarPosition) (f : SplitPosition → ℝ) (hf : MemLp f 2) :
    (∫ p, f p*localizedMode freq u p) =
      ∫ r, verticalCoefficient freq f r*normalizedPlanarMode (r-u) := by
  have hi : Integrable (fun p => f p*localizedMode freq u p)
      ((volume : Measure PlanarPosition).prod (volume : Measure ℝ)) := by
    rw [← Measure.volume_eq_prod]
    exact hf.integrable_mul (localizedMode_memLp hfreq u)
  rw [Measure.volume_eq_prod,integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards [] with r
  unfold verticalCoefficient
  rw [← integral_mul_const]
  apply integral_congr_ae
  filter_upwards [] with z
  unfold localizedMode
  ring

theorem residual_planarCoefficient_orthogonal {freq : ℝ} (hfreq : 0 < freq)
    (u : PlanarPosition) (f : SplitPosition → ℝ) (hf : MemLp f 2) :
    (∫ z, planarCoefficient u (verticalResidual freq f) z*verticalMode freq z) = 0 := by
  rw [planarCoefficient_pair_tensor hfreq u _ (verticalResidual_mass hfreq f hf).1]
  exact verticalResidual_orthogonal hfreq f hf (fun r => normalizedPlanarMode (r-u))
    (normalizedPlanarMode_memLp.comp_measurePreserving (measurePreserving_sub_right volume u))

end ContinuumCoulomb

end

end OAI
