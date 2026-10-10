import OAI.Geometry.RCD.Sobolev.PoissonDefectBudget

namespace OAI

/-! # The full Poisson mass budget in the original normalized source units -/

open Set Metric MeasureTheory

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (hQ : QuadraticCheegerEnergy μ)

/-- Source and curvature terms are paid by the same original normalized
Poisson defect, with a constant independent of the dyadic radius. -/
theorem poisson_pair_mass_units {n : ℕ} {κ root q A : ℝ} {p z : X}
    (S1 : DyadicDistanceSources μ hQ n κ p root)
    (S2 : DyadicDistanceSources μ hQ n κ z root)
    (hκ : 0 ≤ κ) (hq : 0 ≤ q) (i : ℕ) :
    let s := distanceSourceRadius root i
    2 * (q * ((S1.source i).real (ball p s) + (S2.source i).real (ball z s)) +
      κ * A ^ 2 * s ^ 2 * (μ.real (ball p s) + μ.real (ball z s))) ≤
      2 * (q + A ^ 2) * s ^ (n : ℝ) *
        (normalizedPoissonDefect μ hQ S1 i + normalizedPoissonDefect μ hQ S2 i) := by
  intro s
  have h1 := normalizedPoissonDefect_units μ hQ S1 i
  have h2 := normalizedPoissonDefect_units μ hQ S2 i
  have heq : s ^ (n : ℝ) * (normalizedPoissonDefect μ hQ S1 i +
      normalizedPoissonDefect μ hQ S2 i) =
      ((S1.source i).real (ball p s) + (S2.source i).real (ball z s)) +
        κ * s ^ 2 * (μ.real (ball p s) + μ.real (ball z s)) := by
    rw [mul_add, h1, h2]
    ring
  rw [show 2 * (q + A ^ 2) * s ^ (n : ℝ) *
      (normalizedPoissonDefect μ hQ S1 i + normalizedPoissonDefect μ hQ S2 i) =
      2 * (q + A ^ 2) * (s ^ (n : ℝ) *
        (normalizedPoissonDefect μ hQ S1 i + normalizedPoissonDefect μ hQ S2 i)) by ring, heq]
  have hc : 0 ≤ κ * s ^ 2 * (μ.real (ball p s) + μ.real (ball z s)) := by positivity
  have hv : 0 ≤ (S1.source i).real (ball p s) + (S2.source i).real (ball z s) := by positivity
  nlinarith only [mul_nonneg hq hc, mul_nonneg (sq_nonneg A) hv]

end RegularPointCoordinates

end

end OAI
