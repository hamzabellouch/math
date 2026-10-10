import OAI.Geometry.RCD.Harmonic.PinchingEnvelope
import OAI.Geometry.RCD.Sobolev.PoissonDefectBudget

namespace OAI

/-! # A summable source for the actual two-center sharp estimate -/

open MeasureTheory
open scoped BigOperators

noncomputable section
namespace RegularPointCoordinates

/-- The square root is taken only after the two summable energies are
combined. Its square, rather than its square root, is summed. -/
def twoCenterProjectionSource (eta : ℝ) (P Q : ℕ → ℝ) (i : ℕ) : ℝ :=
  Real.sqrt (pinchingEnvelope (7 / 8) (3 / 4) eta P i +
    pinchingEnvelope (7 / 8) (3 / 4) eta Q i)

/-- The actual defects at the two centers and each radial-fit envelope
are dominated by one strictly positive source with a uniform square sum. -/
theorem twoCenterProjectionSource_budget {eta : ℝ} (heta : 0 < eta)
    {P Q : ℕ → ℝ} (hP : ∀ i, 0 ≤ P i) (hQ : ∀ i, 0 ≤ Q i)
    (hPs : Summable P) (hQs : Summable Q) :
    (∀ i, 0 < twoCenterProjectionSource eta P Q i ∧
      P i + Q i ≤ twoCenterProjectionSource eta P Q i ^ 2 ∧
      pinchingEnvelope (7 / 8) (3 / 4) eta Q i ≤ twoCenterProjectionSource eta P Q i ^ 2) ∧
    Summable (fun i => twoCenterProjectionSource eta P Q i ^ 2) ∧
    (∑' i, twoCenterProjectionSource eta P Q i ^ 2) ≤
      64 * (2 * eta + (∑' i, P i) + ∑' i, Q i) := by
  obtain ⟨hEP, hEPsum, hEPi⟩ := pinchingEnvelope_spec (by norm_num : (0 : ℝ) < 7 / 8)
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 3 / 4) (by norm_num) heta hP hPs
  obtain ⟨hEQ, hEQsum, hEQi⟩ := pinchingEnvelope_spec (by norm_num : (0 : ℝ) < 7 / 8)
    (by norm_num) (by norm_num : (0 : ℝ) ≤ 3 / 4) (by norm_num) heta hQ hQs
  have heq (i : ℕ) : twoCenterProjectionSource eta P Q i ^ 2 =
      pinchingEnvelope (7 / 8) (3 / 4) eta P i + pinchingEnvelope (7 / 8) (3 / 4) eta Q i :=
    Real.sq_sqrt (add_nonneg (hEPi i).2.2.le (hEQi i).2.2.le)
  refine ⟨fun i => ?_, ?_, ?_⟩
  · refine ⟨Real.sqrt_pos.mpr (add_pos (hEPi i).2.2 (hEQi i).2.2), ?_, ?_⟩
    · rw [heq]
      exact add_le_add (hEPi i).1 (hEQi i).1
    · rw [heq]
      linarith [(hEPi i).2.2]
  · simpa only [heq] using hEP.add hEQ
  · simp only [heq]
    rw [hEP.tsum_add hEQ]
    norm_num at hEPsum hEQsum
    linarith

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- Specialization to the original positive Poisson defects; no new
source or summability premise is introduced for sharp projection. -/
theorem actual_two_center_projection_budget {μ : Measure X} [IsFiniteMeasureOnCompacts μ]
    {hQ : QuadraticCheegerEnergy μ} {n : ℕ} {κ root : ℝ} {p q : X}
    (S1 : DyadicDistanceSources μ hQ n κ p root)
    (S2 : DyadicDistanceSources μ hQ n κ q root) (hκ : 0 ≤ κ)
    {eta : ℝ} (heta : 0 < eta)
    (hP : Summable (normalizedPoissonDefect μ hQ S1))
    (hQsum : Summable (normalizedPoissonDefect μ hQ S2)) :
    let sigma := twoCenterProjectionSource eta
      (normalizedPoissonDefect μ hQ S1) (normalizedPoissonDefect μ hQ S2)
    (∀ i, 0 < sigma i ∧ normalizedPoissonDefect μ hQ S1 i +
      normalizedPoissonDefect μ hQ S2 i ≤ sigma i ^ 2 ∧
      pinchingEnvelope (7 / 8) (3 / 4) eta (normalizedPoissonDefect μ hQ S2) i ≤ sigma i ^ 2) ∧
    Summable (fun i => sigma i ^ 2) ∧
    (∑' i, sigma i ^ 2) ≤ 64 * (2 * eta +
      (∑' i, normalizedPoissonDefect μ hQ S1 i) + ∑' i, normalizedPoissonDefect μ hQ S2 i) :=
  twoCenterProjectionSource_budget heta
    (normalizedPoissonDefect_nonneg μ hQ S1 hκ)
    (normalizedPoissonDefect_nonneg μ hQ S2 hκ) hP hQsum

end RegularPointCoordinates

end

end OAI
