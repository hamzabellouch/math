import OAI.MeasureTheory.Falconer.Fourier.OriginalStationaryPower
import OAI.MeasureTheory.Falconer.Geometry.FarNormalizedBound

namespace OAI

/-! # Passing pointwise stationary remainders to the original law

Only the added error is measurable here. The stationary kernel itself
enters a nonnegative upper integral and needs no joint spatial regularity.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem lintegral_norm_replacement {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {U : Set X} (hU : MeasurableSet U)
    (f g : X → ℂ) {ε : ℝ} (hε : 0 ≤ ε)
    (herror : ∀ x ∈ U, ‖f x-g x‖ ≤ ε) :
    (∫⁻ x in U, ENNReal.ofReal ‖f x‖ ∂μ) ≤
      (∫⁻ x in U, ENNReal.ofReal ‖g x‖ ∂μ) + ENNReal.ofReal ε * μ U := by
  calc
    _ ≤ ∫⁻ x in U, ENNReal.ofReal ‖g x‖ + ENNReal.ofReal ε ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hU] with x hx
      rw [← ENNReal.ofReal_add (norm_nonneg _) hε]
      apply ENNReal.ofReal_le_ofReal
      calc
        ‖f x‖ = ‖g x+(f x-g x)‖ := by congr 1; ring
        _ ≤ ‖g x‖+‖f x-g x‖ := norm_add_le _ _
        _ ≤ _ := add_le_add le_rfl (herror x hx)
    _ = _ := by rw [lintegral_add_right _ measurable_const,lintegral_const,Measure.restrict_apply_univ]

theorem profileModelMass_inv_four (profile : ℝ → ℝ) (N b : ℕ) :
    (profileModelMass profile N b)⁻¹^4 = ((2:ℝ)^N)^(4*profile ((b:ℝ)/N)) := by
  have hR : 0 < (2:ℝ)^N := by positivity
  rw [profileModelMass,Real.rpow_neg hR.le,inv_inv,← Real.rpow_natCast,← Real.rpow_mul hR.le]
  congr 1
  ring

theorem profile_collision_scale (profile : ℝ → ℝ) (N : ℕ)
    {b t : ℕ} (hbt : b ≤ t) :
    (2:ℝ)^(t-b)*((2:ℝ)^N)^(4*profile ((b:ℝ)/N)) =
      (2:ℝ)^((t:ℝ)-b)*(profileModelMass profile N b)⁻¹^4 := by
  rw [profileModelMass_inv_four,← Nat.cast_sub hbt,Real.rpow_natCast]

end Falconer

end OAI
