import OAI.NumberTheory.EgyptianFractions.DivisorClasses
import OAI.NumberTheory.EgyptianFractions.DivisorMomentFinalBudget

namespace OAI
noncomputable section
open scoped BigOperators
open Filter

namespace Problem337.DivisorClasses

attribute [local instance] Classical.propDecidable

/-- Once the three arithmetic class estimates are supplied, the exact uniform
moment budget follows. The prime-prefix cover and every numerical loss are
discharged here, including the case of an empty intermediate range. -/
theorem eventually_class_budget_assembly (D r C : ℝ)
    (hD : 1 ≤ D) (hr : 0 ≤ r) (hC : 0 ≤ C) :
    ∀ᶠ S : ℝ in atTop, ∀ v Y : ℝ,
      S / (2 * Real.log S) ≤ v → v ≤ D * S →
      Real.exp (v / 2) ≤ Y → Y ≤ Real.exp v →
      ∀ (H : Finset ℕ) (n : ℕ → ℕ) (w : ℕ → ℝ),
      (∀ i ∈ H, 0 ≤ w i) →
      (∑ i ∈ H with LargeClass (n i) v Y, w i) ≤
        2 * Y * Real.exp (r * (1 + Real.log ((D + 1) * S / v)) *
          v ^ (1 / 16 : ℝ) + C * Real.log (1 + Real.log (Real.sqrt Y))) →
      (∑ i ∈ H with SmallClass (n i) S v Y, w i) ≤
        2 * Y * Real.exp (-v / 100) →
      (∀ j : ℕ, (∑ i ∈ H with BandClass (n i) S v Y j, w i) ≤ 2 * Y) →
      (∑ i ∈ H, w i) ≤ Y * Real.exp (S ^ (1 / 4 : ℝ)) := by
  filter_upwards [DyadicBands.eventually_divisor_band_cover D,
    DivisorMomentFinalBudget.eventually_divisor_moment_weighted_budget D r C hD hr hC,
    DivisorMomentFinalBudget.eventually_sqrt_cutoff_window D,
    eventually_ge_atTop (2 : ℝ)] with S hcover hbudget hwindow hS
  intro v Y hvlo hvhi hYlo hYhi H n w hw hlarge hsmall hband
  have hY0 : 0 ≤ Y := (Real.exp_pos (v / 2)).le.trans hYlo
  have hlogS : 0 ≤ Real.log S := Real.log_nonneg (by linarith)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hexists : ∃ J : ℕ, (J : ℝ) ≤ (3 / Real.log 2) * Real.log S ∧
      ∀ x : ℝ, 4 * Real.log S ≤ x → x < v ^ (15 / 16 : ℝ) →
        ∃ j : ℕ, j < J ∧ DyadicBands.InBand (4 * Real.log S) j x := by
    by_cases hrange : 4 * Real.log S ≤ v ^ (15 / 16 : ℝ)
    · exact hcover v hvlo hvhi hrange
    · refine ⟨0, ?_, ?_⟩
      · simp only [Nat.cast_zero]
        positivity
      · intro x hx hxv
        exact (hrange (hx.trans hxv.le)).elim
  obtain ⟨J, hJ, hbands⟩ := hexists
  have hsqrt : 1 ≤ Real.sqrt Y := by
    have := (hwindow v Y hvlo hvhi hYlo hYhi).2.1
    linarith
  have hsum := sum_le_class_bounds H n w S v Y J
    (2 * Y * Real.exp (r * (1 + Real.log ((D + 1) * S / v)) *
      v ^ (1 / 16 : ℝ) + C * Real.log (1 + Real.log (Real.sqrt Y))))
    (2 * Y * Real.exp (-v / 100)) (2 * Y) hsqrt hbands hw hlarge hsmall
    (fun j _ => hband j)
  have hJY : (J : ℝ) * (2 * Y) ≤ Y * ((6 / Real.log 2) * Real.log S) := by
    calc
      _ ≤ (3 / Real.log 2) * Real.log S * (2 * Y) :=
        mul_le_mul_of_nonneg_right hJ (show 0 ≤ 2 * Y by positivity)
      _ = _ := by ring
  have hfinal := hbudget v Y hvlo hvhi hYlo hYhi
  linarith

end Problem337.DivisorClasses

end

end OAI
