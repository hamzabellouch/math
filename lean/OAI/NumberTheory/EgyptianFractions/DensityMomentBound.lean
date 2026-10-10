import OAI.NumberTheory.EgyptianFractions.DensityMomentBridge
import OAI.NumberTheory.EgyptianFractions.UniformDivisorMoment

namespace OAI
noncomputable section
open scoped BigOperators
open Filter

namespace Problem337

/-- The unconditional uniform divisor moment in the density count notation. -/
theorem eventually_density_divisor_moment (D r : ℝ) (hD : 1 ≤ D) (hr : 0 ≤ r) :
    ∀ᶠ S : ℝ in atTop, ∀ (X Y : ℝ) (N : ℕ),
      S / (2 * Real.log S) ≤ Real.log X → Real.log X ≤ D * S →
      Real.sqrt X ≤ Y → Y ≤ X → (N : ℝ) ≤ Real.exp (D * S) →
      (∑ h ∈ Finset.Icc 1 ⌊Y⌋₊, densityDivisorCount X (N + h) ^ r) ≤
        Y * Real.exp (S ^ (1 / 4 : ℝ)) := by
  simpa only [densityDivisorCount_eq_truncated] using
    DivisorMoment.eventually_uniform_divisor_moment D r hD hr

/-- All moments required by the canonical geometric density family hold
unconditionally, simultaneously at each level and for every divisor of its
auxiliary denominator. Only the stated size ranges remain as hypotheses. -/
theorem eventually_residue_level_moment
    (DM η r : ℝ) (hDM : 1 < DM) (hη : 0 < η) (hηhalf : η ≤ 1 / 2)
    (hr : 0 ≤ r) :
    ∀ᶠ S : ℝ in atTop, ∀ C M : ℕ, 0 < C → 0 < M →
      (C : ℝ) ≤ Real.exp (8 * (DM + 2) * S) →
      (M : ℝ) ≤ Real.exp (DM * S) →
      ∀ j : ℕ, j < ResidueLevels.depth ((DM + 2) * S) (ResidueLevels.scale S) η →
      ∀ t : ℕ, t ∣ M →
      (∑ h ∈ Finset.Icc 1
          ⌊ResidueLevels.level ((DM + 2) * S) (ResidueLevels.scale S) η (j + 1)⌋₊,
        densityDivisorCount
          (ResidueLevels.level ((DM + 2) * S) (ResidueLevels.scale S) η j)
          (ResidueLevels.factor ((DM + 2) * S) (ResidueLevels.scale S) η S C j * t + h)
          ^ r) ≤
        ResidueLevels.level ((DM + 2) * S) (ResidueLevels.scale S) η (j + 1) *
          Real.exp (S ^ (1 / 4 : ℝ)) := by
  exact eventually_residue_level_moment_of_uniform DM η r hDM hη hηhalf
    (DivisorMoment.eventually_uniform_divisor_moment (densityMomentParameter DM) r
      (densityMomentParameter_ge_one hDM) hr)

end Problem337

end

end OAI
