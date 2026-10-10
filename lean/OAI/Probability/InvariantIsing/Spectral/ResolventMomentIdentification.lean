import OAI.Probability.InvariantIsing.Spectral.ResolventPowerDerivative

namespace OAI

/-! Equality of positive resolvents determines all their bounded powers. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace InvariantIsing

theorem positiveResolvent_moments_eq (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ t : ℝ, 0 < t → (∫ x, positiveResolventTest t x ∂μ) =
      ∫ x, positiveResolventTest t x ∂ν) :
    ∀ n : ℕ, ∀ t : ℝ, 0 < t →
      (∫ x, (positiveResolventTest t x)^(n+1) ∂μ) =
        ∫ x, (positiveResolventTest t x)^(n+1) ∂ν := by
  intro n
  induction n with
  | zero => simpa only [zero_add,pow_one] using h
  | succ n ih =>
    intro t ht
    have he : (fun s => ∫ x, (positiveResolventTest s x)^(n+1) ∂ν) =ᶠ[𝓝 t]
        fun s => ∫ x, (positiveResolventTest s x)^(n+1) ∂μ := by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      exact (ih s hs).symm
    have hd := ((positiveResolventPower_integral_hasDerivAt μ ht (n+1)).congr_of_eventuallyEq he).unique
      (positiveResolventPower_integral_hasDerivAt ν ht (n+1))
    exact mul_left_cancel₀ (neg_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n))) hd

end InvariantIsing

end

end OAI
