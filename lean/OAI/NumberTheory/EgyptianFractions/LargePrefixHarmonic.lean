import OAI.NumberTheory.EgyptianFractions.LargePrefixClass
import OAI.NumberTheory.EgyptianFractions.HarmonicPrefixBudget

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

/-- The actual large-prefix class has an unconditional harmonic-moment budget.
The finite set is indexed by the positive translation parameter. -/
theorem large_prefix_class_harmonic_bound (r : ℝ) (hr : 0 ≤ r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X W Z L Y : ℝ) (N : ℕ) (A : Finset ℕ),
      1 < X → Real.log X ≤ W → 0 < L → 2 ≤ Z → Z ≤ Y →
      A ⊆ Finset.Icc 1 ⌊Y⌋₊ →
      (∀ h ∈ A, Real.log ((N + h : ℕ) : ℝ) ≤ W) →
      (∀ h ∈ A, InLargePrefixClass Z L (N + h)) →
      (∑ h ∈ A, (truncatedDivisorCount X (N + h) : ℝ) ^ r) ≤
        2 * Y * Real.exp (r * ((1 + Real.log (W / Real.log X)) * Real.log X / L) +
          C * Real.log (1 + Real.log Z)) := by
  obtain ⟨C, hC, hbudget⟩ := DivisorMoment.real_shifted_harmonic_prefix_budget r
  refine ⟨C, hC, ?_⟩
  intro X W Z L Y N A hX hXW hL hZ hZY hA hW hclass
  apply hbudget N Y A Z
    (r * ((1 + Real.log (W / Real.log X)) * Real.log X / L))
    (fun h => (truncatedDivisorCount X (N + h) : ℝ) ^ r) hZ hZY hA
  intro h hh
  have hn : 0 < N + h := by
    have := (Finset.mem_Icc.mp (hA hh)).1
    omega
  obtain ⟨d, hd0, hd, hdZ, hmajor⟩ :=
    large_prefix_class_majorant X W r Z L hn hX hXW (hW h hh) hr hL (hclass h hh)
  exact ⟨d, hd0, hdZ, hd, by simpa only [mul_comm] using hmajor⟩

/-- The manuscript's square-root cutoff and large-next-prime threshold,
with the harmonic divisor sum fully discharged. -/
theorem large_prefix_class_sqrt_harmonic_bound (r : ℝ) (hr : 0 ≤ r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X W Y : ℝ) (N : ℕ) (A : Finset ℕ),
      1 < X → Real.log X ≤ W → 4 ≤ Y →
      A ⊆ Finset.Icc 1 ⌊Y⌋₊ →
      (∀ h ∈ A, Real.log ((N + h : ℕ) : ℝ) ≤ W) →
      (∀ h ∈ A, InLargePrefixClass (Real.sqrt Y)
        ((Real.log X) ^ (15 / 16 : ℝ)) (N + h)) →
      (∑ h ∈ A, (truncatedDivisorCount X (N + h) : ℝ) ^ r) ≤
        2 * Y * Real.exp (r * (1 + Real.log (W / Real.log X)) *
          (Real.log X) ^ (1 / 16 : ℝ) +
          C * Real.log (1 + Real.log (Real.sqrt Y))) := by
  obtain ⟨C, hC, hbudget⟩ := large_prefix_class_harmonic_bound r hr
  refine ⟨C, hC, ?_⟩
  intro X W Y N A hX hXW hY hA hW hclass
  have hv : 0 < Real.log X := Real.log_pos hX
  have hZ : 2 ≤ Real.sqrt Y :=
    (Real.le_sqrt (by norm_num) (by linarith)).2 (by nlinarith)
  have hZY : Real.sqrt Y ≤ Y := by
    apply (Real.sqrt_le_iff).2
    constructor <;> nlinarith
  have hpow : Real.log X / (Real.log X) ^ (15 / 16 : ℝ) =
      (Real.log X) ^ (1 / 16 : ℝ) := by
    calc
      _ = (Real.log X) ^ (1 : ℝ) / (Real.log X) ^ (15 / 16 : ℝ) := by
        rw [Real.rpow_one]
      _ = (Real.log X) ^ ((1 : ℝ) - 15 / 16) := (Real.rpow_sub hv _ _).symm
      _ = _ := by norm_num
  have hH : r * ((1 + Real.log (W / Real.log X)) * Real.log X /
      (Real.log X) ^ (15 / 16 : ℝ)) =
      r * (1 + Real.log (W / Real.log X)) * (Real.log X) ^ (1 / 16 : ℝ) := by
    rw [mul_div_assoc, hpow]
    ring
  simpa only [hH] using hbudget X W (Real.sqrt Y)
    ((Real.log X) ^ (15 / 16 : ℝ)) Y N A hX hXW (by positivity) hZ hZY hA hW hclass

end Problem337

end

end OAI
