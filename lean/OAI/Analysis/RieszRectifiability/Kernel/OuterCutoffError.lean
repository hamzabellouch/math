import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.LocalizedRieszPairingBounds
import OAI.Analysis.RieszRectifiability.Kernel.PairingLocalizationIndependence

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem riesz_pairing_outer_cutoff_error_bound {d : ℕ} (m : ℕ) (G : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] (hg : GlobalUpperGrowth m G μ)
    (e : Ambient d) (φ : Ambient d → ℝ) (L : ℝ≥0) (hφ : LipschitzWith L φ)
    (z a : Ambient d) (H R T : ℝ) (hH : 0 ≤ H) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (hcontain : ball z R ⊆ ball a T)
    (hsupport : ∀ x, φ x ≠ 0 → dist x z ≤ H) :
    |rieszScalarPairing m μ z R e φ -
      rieszScalarPairing m (μ.restrict (ball a T)) z R e φ| ≤
      (2 ^ (m + 1) + (m + 1 : ℝ) * 2 ^ (m + 2)) *
        (‖e‖ * H * (∫ x in ball z R, |φ x| ∂μ)) * (2 * (G * 2 ^ m / R)) := by
  have hi := rieszFarIntegrand_integrable_of_compact_lipschitz m G μ hg e φ L hφ
    z H R hH hR hHR hsupport
  have hb := rieszFarIntegrand_integral_abs_bound m G μ hg e φ L hφ z H R
    hH hR hHR hsupport
  rw [rieszScalarPairing_restrict_outer_ball m μ z a R T hcontain e φ]
  unfold rieszScalarPairing
  dsimp only
  rw [add_sub_add_left_eq_sub]
  rw [← setIntegral_compl (MeasurableSet.univ.prod measurableSet_ball) hi]
  calc
    _ ≤ ∫ q in (univ ×ˢ ball a T)ᶜ, |rieszFarIntegrand m e φ z q|
        ∂(μ.restrict (ball z R)).prod (μ.restrict (closedExterior z R)) :=
      abs_integral_le_integral_abs
    _ ≤ ∫ q, |rieszFarIntegrand m e φ z q|
        ∂(μ.restrict (ball z R)).prod (μ.restrict (closedExterior z R)) :=
      integral_mono_measure Measure.restrict_le_self
        (Filter.Eventually.of_forall fun q => abs_nonneg _) hi.abs
    _ ≤ _ := hb

end

end RieszRectifiability

end OAI
