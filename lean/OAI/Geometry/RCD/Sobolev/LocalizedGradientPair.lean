import OAI.Analysis.RCDHeat.ExistingAnalytic

namespace OAI

/-! # Localizing the energy pairing under normalized volume -/

open Set Filter Metric MeasureTheory
open scoped ENNReal

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

omit [BorelSpace X] [ProperSpace X] in
theorem integral_uniformOn_of_support {Ω : Set X} {v : X → ℝ}
    (hv : tsupport v ⊆ Ω) :
    (∫ x, v x ∂uniformOn μ Ω) = (μ Ω).toReal⁻¹ * ∫ x, v x ∂μ := by
  rw [uniformOn, integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul]
  congr 1
  apply setIntegral_eq_integral_of_ae_compl_eq_zero
  exact Eventually.of_forall fun x hx => by
    by_contra hn
    exact hx (hv (subset_tsupport v hn))

theorem weightedGradientPair_uniformOn {Ω : Set X} (hΩ0 : μ Ω ≠ 0)
    (f g : SobolevSpace μ hQ) (v : X → ℝ) (hv : tsupport v ⊆ Ω)
    (hrep : SobolevSpace.toLp μ hQ g =ᵐ[μ] v) :
    weightedGradientPair μ hQ (uniformOn μ Ω) f g =
      (μ Ω).toReal⁻¹ * energyForm μ hQ f g := by
  have hC : (μ Ω)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hΩ0
  have hν : uniformOn μ Ω ≤ (μ Ω)⁻¹ • μ := by
    intro S
    exact mul_le_mul_right (Measure.restrict_le_self (μ := μ) (s := Ω) S) _
  rw [weightedGradientPair_eq_bracket μ hQ hC hν,
    ← integral_localGamma μ hQ hC hν, uniformOn, integral_smul_measure,
    ENNReal.toReal_inv, smul_eq_mul]
  congr 1
  rw [← integral_localGamma_eq_energyForm]
  apply setIntegral_eq_integral_of_ae_compl_eq_zero
  filter_upwards [hrep, localGamma_zero_on_level μ hQ g f 0,
    localGamma_comm μ hQ f g] with x hx hz hc hxΩ
  have hvx : v x = 0 := by
    by_contra hn
    exact hxΩ (hv (subset_tsupport v hn))
  rw [hc]
  exact hz (hx.trans hvx)

end RegularPointCoordinates

end OAI
