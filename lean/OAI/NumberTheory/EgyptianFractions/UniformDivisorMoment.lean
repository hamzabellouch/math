import OAI.NumberTheory.EgyptianFractions.SmallPrimeMoment
import OAI.NumberTheory.EgyptianFractions.IntermediateBandBudget
import OAI.NumberTheory.EgyptianFractions.LargeClassUniform
import OAI.NumberTheory.EgyptianFractions.DivisorClassAssembly

namespace OAI
noncomputable section

open Filter
open scoped BigOperators

namespace Problem337.DivisorMoment

attribute [local instance] Classical.propDecidable

/-- The complete uniform shifted divisor moment, with the upper cutoff
parameterized exponentially. All three prime-factor classes are estimated
unconditionally; the threshold depends only on the fixed `D` and `r`. -/
theorem eventually_uniform_divisor_moment_exp (D r : ℝ)
    (hD : 1 ≤ D) (hr : 0 ≤ r) :
    ∀ᶠ S : ℝ in atTop, ∀ v Y : ℝ, ∀ N : ℕ,
      S / (2 * Real.log S) ≤ v → v ≤ D * S →
      Real.exp (v / 2) ≤ Y → Y ≤ Real.exp v →
      (N : ℝ) ≤ Real.exp (D * S) →
      (∑ h ∈ Finset.Icc 1 ⌊Y⌋₊,
        (truncatedDivisorCount (Real.exp v) (N + h) : ℝ) ^ r) ≤
        Y * Real.exp (S ^ (1 / 4 : ℝ)) := by
  obtain ⟨C, hC, hlarge⟩ := eventually_large_class_moment_bound_exp D r hD hr
  filter_upwards [hlarge, small_class_truncated_moment_bound D r hD hr,
    eventually_intermediate_band_budget D r hD hr,
    DivisorClasses.eventually_class_budget_assembly D r C hD hr hC.le]
    with S hlarge hsmall hband hassemble
  intro v Y N hvlo hvhi hYlo hYhi hN
  have hYpos : 0 < Y := (Real.exp_pos (v / 2)).trans_le hYlo
  have hsqrt : Real.sqrt (Real.exp v) = Real.exp (v / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.exp_mul]
    congr 1
    ring
  apply hassemble v Y hvlo hvhi hYlo hYhi (Finset.Icc 1 ⌊Y⌋₊)
    (fun h => N + h) (fun h => (truncatedDivisorCount (Real.exp v) (N + h) : ℝ) ^ r)
  · intro h hh
    positivity
  · exact hlarge v Y N hvlo hvhi hYlo hYhi hN
  · simpa only [Real.log_exp] using hsmall (Real.exp v) Y N
      (by simpa only [Real.log_exp] using hvlo)
      (by simpa only [Real.log_exp] using hvhi)
      (by simpa only [hsqrt] using hYlo) hYhi hN
  · intro j
    by_cases hj : 4 * Real.log S * 2 ^ j ≤ v ^ (15 / 16 : ℝ)
    · exact hband v Y N j hvlo hvhi hYlo hYhi hN hj
    · have hempty : (Finset.Icc 1 ⌊Y⌋₊).filter
          (fun h => DivisorClasses.BandClass (N + h) S v Y j) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro h hh hb
        exact hj (DivisorClasses.band_scale_lt hb).le
      simp only [hempty, Finset.sum_empty]
      positivity

/-- Uniform divisor moments with real cutoffs. The statement also covers a real
interval length through its floor. -/
theorem eventually_uniform_divisor_moment (D r : ℝ)
    (hD : 1 ≤ D) (hr : 0 ≤ r) :
    ∀ᶠ S : ℝ in atTop, ∀ X Y : ℝ, ∀ N : ℕ,
      S / (2 * Real.log S) ≤ Real.log X → Real.log X ≤ D * S →
      Real.sqrt X ≤ Y → Y ≤ X → (N : ℝ) ≤ Real.exp (D * S) →
      (∑ h ∈ Finset.Icc 1 ⌊Y⌋₊,
        (truncatedDivisorCount X (N + h) : ℝ) ^ r) ≤
        Y * Real.exp (S ^ (1 / 4 : ℝ)) := by
  filter_upwards [eventually_uniform_divisor_moment_exp D r hD hr,
    eventually_ge_atTop (2 : ℝ)] with S hmoment hS
  intro X Y N hvlo hvhi hYlo hYhi hN
  have hSpos : 0 < S := by linarith
  have hlogS : 0 < Real.log S := Real.log_pos (by linarith)
  have hlogX : 0 < Real.log X :=
    (by positivity : 0 < S / (2 * Real.log S)).trans_le hvlo
  have hXnonneg : 0 ≤ X := (Real.sqrt_nonneg X).trans (hYlo.trans hYhi)
  have hX : 1 < X := (Real.log_pos_iff hXnonneg).mp hlogX
  have hXpos : 0 < X := by linarith
  have hsqrt : Real.exp (Real.log X / 2) = Real.sqrt X := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hXpos]
    congr 1
    ring
  simpa only [Real.exp_log hXpos] using hmoment (Real.log X) Y N hvlo hvhi
    (by simpa only [hsqrt] using hYlo)
    (by simpa only [Real.exp_log hXpos] using hYhi) hN

end Problem337.DivisorMoment

end

end OAI
