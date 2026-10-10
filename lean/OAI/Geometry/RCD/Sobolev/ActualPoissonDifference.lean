import OAI.Geometry.RCD.Sobolev.ActualPoissonMass

namespace OAI

/-! # Full Bochner mass of the actual two-center harmonic difference -/

open Set Metric MeasureTheory
open scoped NNReal ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (hQ : QuadraticCheegerEnergy μ)
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The scalar shifts cancel for the difference of two actual same-scale
replacements. The ordinary full Bochner mass is bounded by the sum of their
two actual source budgets, including all singular parts. -/
theorem actual_poisson_difference_mass_le
    {n : ℕ} {κ r0 B J C A Cχ : ℝ} {p₁ p₂ z : X}
    {S₁ : DyadicDistanceSources μ hQ n κ p₁ r0}
    {S₂ : DyadicDistanceSources μ hQ n κ p₂ r0}
    (T₁ : DyadicDistanceReplacements μ hQ S₁ B J C)
    (T₂ : DyadicDistanceReplacements μ hQ S₂ B J C) (i : ℕ)
    (hκ : 0 ≤ κ) (hCχ : 0 ≤ Cχ)
    (hroom₁ : dist z p₁ ≤ distanceSourceRadius r0 i / 4)
    (hroom₂ : dist z p₂ ≤ distanceSourceRadius r0 i / 4)
    {U : E →L[ℝ] SobolevSpace μ hQ} {M : PositiveBilinearMeasure X E}
    {L : ℝ≥0} {v₁ v₂ : E} (ell : E →ₗ[ℝ] ℝ)
    [IsFiniteMeasure (μ.restrict (ball z (2 * (distanceSourceRadius r0 i / 32))))]
    (G₁ : LocalHarmonicEnergy μ hQ U M κ z (distanceSourceRadius r0 i / 32) L v₁)
    (G₂ : LocalHarmonicEnergy μ hQ U M κ z (distanceSourceRadius r0 i / 32) L v₂)
    (hv₁ : U v₁ = T₁.replacement i) (hv₂ : U v₂ = T₂.replacement i)
    (hell₁ : ell v₁ = (n : ℝ) + κ * (4 * distanceSourceRadius r0 i) ^ 2)
    (hell₂ : ell v₂ = (n : ℝ) + κ * (4 * distanceSourceRadius r0 i) ^ 2)
    (hshift : ShiftedBochnerLowerBound M
      (μ.restrict (ball z (2 * (distanceSourceRadius r0 i / 32)))) ell n)
    (χ : GoodLaplacianCutoff μ hQ z (distanceSourceRadius r0 i / 64) Cχ)
    (hgrad₁ : ∀ᵐ x ∂μ.restrict (ball z (2 * (distanceSourceRadius r0 i / 32))),
      localGamma μ hQ (T₁.replacement i) (T₁.replacement i) x ≤
        A ^ 2 * (distanceSourceRadius r0 i) ^ 2)
    (hgrad₂ : ∀ᵐ x ∂μ.restrict (ball z (2 * (distanceSourceRadius r0 i / 32))),
      localGamma μ hQ (T₂.replacement i) (T₂.replacement i) x ≤
        A ^ 2 * (distanceSourceRadius r0 i) ^ 2) :
    let s := distanceSourceRadius r0 i
    (M.measure (v₂ - v₁)).real (ball z (s / 64)) ≤
      2 * (4096 * Cχ * (J + B / 2) *
        ((S₁.source i).real (ball p₁ s) + (S₂.source i).real (ball p₂ s)) +
        κ * A ^ 2 * s ^ 2 * (μ.real (ball p₁ s) + μ.real (ball p₂ s))) := by
  have hm₁ := T₁.shifted_mass_le μ hQ i hκ hCχ hroom₁ ell G₁ hv₁ hell₁ hshift χ hgrad₁
  have hm₂ := T₂.shifted_mass_le μ hQ i hκ hCχ hroom₂ ell G₂ hv₂ hell₂ hshift χ hgrad₂
  have ht := ShiftedBochnerMeasure.difference_mass_le M
    (μ.restrict (ball z (2 * (distanceSourceRadius r0 i / 32)))) ell (n : ℝ) hshift
    v₂ v₁ 1 1 (ball z (distanceSourceRadius r0 i / 64)) measurableSet_ball
  rw [sub_self, ShiftedBochnerMeasure.zero_shift] at ht
  exact ht.trans (by nlinarith [hm₁, hm₂])

end RegularPointCoordinates

end

end OAI
