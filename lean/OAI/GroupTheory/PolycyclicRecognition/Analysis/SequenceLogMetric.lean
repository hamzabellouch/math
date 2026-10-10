import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanNMetric
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequenceSubexponentialOperations

namespace OAI

/-! # Turning the source bridge's logarithmic size into metric length -/

namespace PolycyclicRecognition

open Filter

/-- A subexponential logarithmic radius contributes an arbitrarily small
linear error; the fixed exponential rate remains explicit. -/
theorem metric_bound_of_sequence_exponential_coordinates
    {V G : Type*} [PseudoMetricSpace G] [One G]
    (Exp : V → G) (size : V → ℝ) (hsize : ∀ v, 0 ≤ size v)
    {D : ℝ} (hD : 0 ≤ D)
    (hmetric : ∀ v, dist 1 (Exp v) ≤ D * Real.log (2 + size v))
    (scale R : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (hscale0 : ∀ n, 0 ≤ scale n) (hR0 : ∀ n, 0 ≤ R n)
    (hR : HasSubexponentialUpperBoundSeq scale R) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ δ : ℝ, 0 ≤ δ → ∀ v : V,
      size v ≤ R n * Real.exp (δ * scale n) →
      dist 1 (Exp v) ≤ D * (δ + ε) * scale n := by
  have hsum := (sequence_subexponential_upper_const hscale 2).add hR hscale
  intro ε hε
  filter_upwards [hsum ε hε] with n hn δ hδ v hv
  have hlog : Real.log (2 + R n) ≤ ε * scale n := by
    have hh := Real.log_le_log (by linarith [hR0 n]) hn
    simpa only [Real.log_exp] using hh
  calc
    _ ≤ D * Real.log (2 + size v) := hmetric v
    _ ≤ D * Real.log (2 + R n * Real.exp (δ * scale n)) :=
      mul_le_mul_of_nonneg_left
        (Real.log_le_log (by linarith [hsize v]) (by linarith)) hD
    _ ≤ D * (Real.log (2 + R n) + scale n * δ) :=
      mul_le_mul_of_nonneg_left (by
        simpa only [mul_comm δ (scale n)] using
          log_two_add_exp_le (hR0 n) hδ (hscale0 n)) hD
    _ ≤ D * (ε * scale n + scale n * δ) :=
      mul_le_mul_of_nonneg_left (by linarith) hD
    _ = _ := by ring

end PolycyclicRecognition

end OAI
