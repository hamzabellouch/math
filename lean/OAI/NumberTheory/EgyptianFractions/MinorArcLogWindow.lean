import OAI.NumberTheory.EgyptianFractions.MinorArcRealWindow
import OAI.NumberTheory.EgyptianFractions.MinorArcBudget

namespace OAI
noncomputable section
open Filter Asymptotics

namespace Problem337.MinorArc

/-- The usual logarithmic major arcs leave only phases admitting an actual
coprime rational approximation in the required real denominator window.
The onset is uniform in the phase. -/
theorem eventually_exists_minor_fraction_log_window (A : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 →
      x ∉ ThreePrimeAnalysis.majorArcUnion ⌊Real.log X ^ A⌋₊
        (2 * Real.log X ^ A / X) →
      ∃ a : ℤ, ∃ q : ℕ,
        Real.log X ^ A ≤ (q : ℝ) ∧ (q : ℝ) ≤ X / Real.log X ^ A ∧
        0 < q ∧ IsCoprime a (q : ℤ) ∧
        |x - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2 := by
  have hlittle : (fun X : ℝ => Real.log X ^ A) =o[atTop] (fun X => X) := by
    simpa only [Real.rpow_natCast, Real.rpow_one] using
      (isLittleO_log_rpow_rpow_atTop (A : ℝ) (by norm_num : (0 : ℝ) < 1))
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    hlittle.bound (by norm_num : (0 : ℝ) < 1 / 4)] with X hX hsmall
  have hlog : 0 < Real.log X := Real.log_pos hX
  have hX0 : 0 < X := by linarith
  have hsmall' : Real.log X ^ A ≤ (1 / 4 : ℝ) * X := by
    simpa only [Real.norm_of_nonneg (pow_nonneg hlog.le A),
      Real.norm_of_nonneg hX0.le] using hsmall
  intro x hx hminor
  exact exists_minor_fraction_real_window (pow_pos hlog A) (by linarith) hx hminor

/-- A denominator supplied by the genuine Dirichlet minor-arc geometry also
satisfies the full scalar Vaughan budget, uniformly in the phase. This does
not assert an exponential-sum estimate. -/
theorem eventually_minor_fraction_with_vaughan_budget
    (B D : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ X : ℝ in atTop, ∀ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 →
      x ∉ ThreePrimeAnalysis.majorArcUnion
        ⌊Real.log X ^ (2 * (B + D + 2))⌋₊
        (2 * Real.log X ^ (2 * (B + D + 2)) / X) →
      ∃ a : ℤ, ∃ q : ℕ,
        Real.log X ^ (2 * (B + D + 2)) ≤ (q : ℝ) ∧
        (q : ℝ) ≤ X / Real.log X ^ (2 * (B + D + 2)) ∧
        0 < q ∧ IsCoprime a (q : ℤ) ∧
        |x - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2 ∧
        C * (X / Real.sqrt q + X ^ (4 / 5 : ℝ) + Real.sqrt (X * q)) *
          Real.log X ^ B ≤ X / Real.log X ^ D := by
  filter_upwards [eventually_exists_minor_fraction_log_window (2 * (B + D + 2)),
    ThreePrimeAnalysis.eventually_vaughan_envelope_le_power_log_budget B D C hC]
    with X hgeom hbudget
  intro x hx hminor
  obtain ⟨a, q, hlow, hupp, hq, hcop, happ⟩ := hgeom x hx hminor
  exact ⟨a, q, hlow, hupp, hq, hcop, happ, hbudget q hlow hupp⟩

end Problem337.MinorArc

end

end OAI
