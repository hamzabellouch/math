import Mathlib
import OAI.Analysis.RieszRectifiability.Limits.LipschitzSquareWeakLimit

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Filter Topology
open scoped NNReal

theorem strong_height_convergence_of_lipschitz_representative {d : ℕ}
    (μ : ℕ → FiniteMeasure (Ambient d)) (ν : FiniteMeasure (Ambient d))
    (hweak : Tendsto μ atTop (𝓝 ν)) (a : Ambient d) (R : ℝ)
    (hμ : ∀ j, ∀ᵐ x ∂(μ j : Measure (Ambient d)), x ∈ ball a R)
    (hν : ∀ᵐ x ∂(ν : Measure (Ambient d)), x ∈ ball a R)
    (w : ℕ → Ambient d → ℝ) (hw : ∀ j, MemLp (w j) 2 (μ j : Measure (Ambient d)))
    (f v : Ambient d → ℝ) (L : ℝ≥0) (hv : LipschitzWith L v)
    (hfv : f =ᵐ[(ν : Measure (Ambient d))] v)
    (hsecond : Tendsto (fun j => ∫ x, w j x ^ 2 ∂(μ j : Measure (Ambient d))) atTop
      (𝓝 (∫ x, f x ^ 2 ∂(ν : Measure (Ambient d)))))
    (hmoment : ∀ (ψ : Ambient d → ℝ) (J B : ℝ≥0), HasCompactSupport ψ →
      LipschitzWith J ψ → (∀ x, |ψ x| ≤ (B : ℝ)) →
      Tendsto (fun j => ∫ x, w j x * ψ x ∂(μ j : Measure (Ambient d))) atTop
        (𝓝 (∫ x, f x * ψ x ∂(ν : Measure (Ambient d))))) :
    Tendsto (fun j => ∫ x, (w j x - v x) ^ 2 ∂(μ j : Measure (Ambient d)))
      atTop (𝓝 0) := by
  have hvj : ∀ j, MemLp v 2 (μ j : Measure (Ambient d)) :=
    fun j => lipschitz_memLp_of_ae_ball _ a R (hμ j) v L hv
  have hcross := compact_moments_extend_on_ball (fun j => (μ j : Measure (Ambient d)))
    (ν : Measure (Ambient d)) a R hμ hν w f hmoment v L hv
  have hcross_eq : (∫ x, f x * v x ∂(ν : Measure (Ambient d))) =
      ∫ x, f x ^ 2 ∂(ν : Measure (Ambient d)) := by
    apply integral_congr_ae
    filter_upwards [hfv] with x hx
    rw [hx, pow_two]
  rw [hcross_eq] at hcross
  have hsquare := lipschitz_square_integral_tendsto_of_ae_ball μ ν hweak a R hμ hν v L hv
  have hsquare_eq : (∫ x, v x ^ 2 ∂(ν : Measure (Ambient d))) =
      ∫ x, f x ^ 2 ∂(ν : Measure (Ambient d)) := by
    apply integral_congr_ae
    filter_upwards [hfv] with x hx
    rw [hx]
  rw [hsquare_eq] at hsquare
  exact squared_error_tendsto_zero_of_moments (fun j => (μ j : Measure (Ambient d)))
    w v (∫ x, f x ^ 2 ∂(ν : Measure (Ambient d)))
    (fun j => (hw j).integrable_sq) (fun j => (hw j).integrable_mul (hvj j))
    (fun j => (hvj j).integrable_sq) hsecond hcross hsquare

end

end RieszRectifiability

end OAI
