import OAI.Analysis.CircleDomains.Topology.ExteriorCoefficientCircle
import OAI.Analysis.CircleDomains.Uniformization.FiniteCoefficientRadial
import OAI.Analysis.CircleDomains.Sobolev.CircleAverageAngularIntegral
import OAI.Analysis.CircleDomains.Sobolev.ExteriorAnnulusArea

namespace OAI

/-! Every finite initial family of Laurent coefficients is paid for by
the exact derivative energy of each exterior annulus. -/
open Set Filter Function Metric Real MeasureTheory Asymptotics Bornology
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma exterior_derivative_coefficient_angular {F : ℂ → ℂ} {R r : ℝ}
    (hR : 0 < R) (hF : DifferentiableOn ℂ F {z | R < ‖z‖})
    (ht : Tendsto (fun z => F z-z) (cobounded ℂ) (𝓝 0)) (hr : R < r) (N : ℕ) :
    ENNReal.ofReal (2*Real.pi*(1+∑ n ∈ Finset.range N,
      ((n : ℝ)+1)^2*‖principalLaurentCoefficient F n‖^2*(r⁻¹)^(2*(n+2)))) ≤
      ∫⁻ θ in Ioo (-Real.pi) Real.pi, ENNReal.ofReal (‖deriv F (circleMap 0 r θ)‖^2) := by
  rw [← circleAverage_angular_lintegral (q := fun z => ‖deriv F z‖^2) (hR.trans hr)
    ((exterior_derivative_continuousOn_circle hF hr).norm.pow 2)
    (fun _ _ => sq_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_left (exterior_derivative_finite_coefficients hR hF ht hr N)
    (by positivity)

lemma exterior_annulus_finite_coefficients {F : ℂ → ℂ} {R a b : ℝ}
    (hR : 0 < R) (hF : DifferentiableOn ℂ F {z | R < ‖z‖})
    (ht : Tendsto (fun z => F z-z) (cobounded ℂ) (𝓝 0))
    (ha : R < a) (hab : a < b) (N : ℕ) :
    Real.pi*(b^2-a^2)+Real.pi*∑ n ∈ Finset.range N,
      ((n : ℝ)+1)*‖principalLaurentCoefficient F n‖^2*
        ((a⁻¹)^(2*(n+1))-(b⁻¹)^(2*(n+1))) ≤
      ∫ z in {z : ℂ | a < ‖z‖ ∧ ‖z‖ < b}, ‖deriv F z‖^2 := by
  let d : ℕ → ℝ := fun n => ‖principalLaurentCoefficient F n‖^2
  have hn : ∀ n, 0 ≤ d n := fun n => sq_nonneg _
  have hle : (∫⁻ r in Ioo a b, ENNReal.ofReal (finiteCoefficientRadialDensity d N r)) ≤
      ∫⁻ z in {z : ℂ | a < ‖z‖ ∧ ‖z‖ < b}, ENNReal.ofReal (‖deriv F z‖^2) := by
    rw [lintegral_circleMap_annulus _ ((measurable_deriv F).norm.pow_const 2).ennreal_ofReal
      (hR.trans ha).le]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    have hrp : 0 ≤ r := (hR.trans (ha.trans hr.1)).le
    have he : finiteCoefficientRadialDensity d N r =
        r*(2*Real.pi*(1+∑ n ∈ Finset.range N,
          ((n : ℝ)+1)^2*‖principalLaurentCoefficient F n‖^2*(r⁻¹)^(2*(n+2)))) := by
      dsimp only [finiteCoefficientRadialDensity, d]
      ring
    rw [he, ENNReal.ofReal_mul hrp]
    gcongr
    exact exterior_derivative_coefficient_angular hR hF ht (ha.trans hr.1) N
  rw [← ofReal_integral_eq_lintegral_ofReal (finiteCoefficientRadialDensity_integrable
    (hR.trans ha) d N) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      exact finiteCoefficientRadialDensity_nonneg hn N (hR.trans (ha.trans hr.1)).le),
    ← ofReal_integral_eq_lintegral_ofReal (exterior_annulus_energy_integrable hF ha)
      (Eventually.of_forall (fun z => sq_nonneg ‖deriv F z‖))] at hle
  have hh := (ENNReal.ofReal_le_ofReal_iff (integral_nonneg
    (fun z => sq_nonneg ‖deriv F z‖))).mp hle
  rw [finiteCoefficientRadialDensity_integral (hR.trans ha) hab d N] at hh
  exact hh

end CircleDomainRigidity

end

end OAI
