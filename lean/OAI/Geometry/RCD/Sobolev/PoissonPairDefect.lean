import OAI.Geometry.RCD.Sobolev.PoissonDefectBudget

namespace OAI

/-! # The full two-center source in the common Poisson defect units -/

open Set Metric MeasureTheory

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (hQ : QuadraticCheegerEnergy μ)

/-- Both positive source masses and the curvature remainder are controlled
by the sum of the two original normalized defects. -/
theorem poisson_pair_defect_bound {n : ℕ} {κ r0 : ℝ} {p₁ p₂ : X}
    (S₁ : DyadicDistanceSources μ hQ n κ p₁ r0)
    (S₂ : DyadicDistanceSources μ hQ n κ p₂ r0) (i : ℕ)
    {C A : ℝ} (hκ : 0 ≤ κ) (hC : 0 ≤ C) :
    let s := distanceSourceRadius r0 i
    C * ((S₁.source i).real (ball p₁ s) + (S₂.source i).real (ball p₂ s)) +
      κ * A ^ 2 * s ^ 2 * (μ.real (ball p₁ s) + μ.real (ball p₂ s)) ≤
      (C + A ^ 2) * s ^ (n : ℝ) *
        (normalizedPoissonDefect μ hQ S₁ i + normalizedPoissonDefect μ hQ S₂ i) := by
  dsimp only
  let s := distanceSourceRadius r0 i
  have hu : s ^ (n : ℝ) *
      (normalizedPoissonDefect μ hQ S₁ i + normalizedPoissonDefect μ hQ S₂ i) =
      (S₁.source i).real (ball p₁ s) + (S₂.source i).real (ball p₂ s) +
        κ * s ^ 2 * (μ.real (ball p₁ s) + μ.real (ball p₂ s)) := by
    rw [mul_add, normalizedPoissonDefect_units μ hQ S₁ i,
      normalizedPoissonDefect_units μ hQ S₂ i]
    ring
  have hsource : 0 ≤ (S₁.source i).real (ball p₁ s) + (S₂.source i).real (ball p₂ s) := by positivity
  have hcurv : 0 ≤ κ * s ^ 2 * (μ.real (ball p₁ s) + μ.real (ball p₂ s)) := by positivity
  calc
    _ ≤ (C + A ^ 2) *
        ((S₁.source i).real (ball p₁ s) + (S₂.source i).real (ball p₂ s) +
          κ * s ^ 2 * (μ.real (ball p₁ s) + μ.real (ball p₂ s))) := by
      nlinarith only [mul_nonneg (sq_nonneg A) hsource, mul_nonneg hC hcurv]
    _ = _ := by rw [← hu]; ring

end RegularPointCoordinates

end

end OAI
