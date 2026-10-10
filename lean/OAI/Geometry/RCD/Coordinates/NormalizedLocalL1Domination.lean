import OAI.Geometry.RCD.Metric.ProbabilityDominationL1

namespace OAI

/-! # Vanishing local errors under normalized bounded compression -/

open Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MeasurableSpace X]

theorem normalized_local_L1_domination (μ : Measure X) (S : ℕ → Set X)
    (ν : ℕ → Measure X) (f : ℕ → X → ℝ) {C : ℝ} (hC : 0≤C)
    (hpos : ∀ k, 0<μ.real (S k))
    (hν : ∀ k, ν k≤ENNReal.ofReal (C/μ.real (S k)) • μ.restrict (S k))
    (hf : ∀ k, IntegrableOn (f k) (S k) μ)
    (hlim : Tendsto (fun k => (μ.real (S k))⁻¹*
      ∫ x in S k, |f k x| ∂μ) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, f k x ∂ν k) atTop (𝓝 0) := by
  apply squeeze_zero_norm
  · intro k
    have hh := integral_difference_le_of_domination (μ.restrict (S k)) (ν k)
      ENNReal.ofReal_ne_top (hν k) (hf k) (integrable_zero X ℝ _)
    simp only [Pi.zero_apply,integral_zero,dist_zero_right,Real.norm_eq_abs,sub_zero,
      ENNReal.toReal_ofReal (div_nonneg hC (hpos k).le)] at hh
    calc
      ‖∫ x, f k x ∂ν k‖=|∫ x, f k x ∂ν k| := Real.norm_eq_abs _
      _≤(C/μ.real (S k))*(∫ x in S k, |f k x| ∂μ) := hh
      _=C*((μ.real (S k))⁻¹*(∫ x in S k, |f k x| ∂μ)) := by ring
  · simpa only [mul_zero] using hlim.const_mul C

end RegularPointCoordinates

end

end OAI
