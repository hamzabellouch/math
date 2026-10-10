import OAI.NumberTheory.EgyptianFractions.HarmonicMoment
import OAI.NumberTheory.EgyptianFractions.DivisorPrefixCounting

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337.DivisorMoment

/-- Summing a harmonic divisor majorant over selected short-interval prefixes. -/
theorem harmonic_prefix_budget (r : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N Y : ℕ) (A : Finset ℕ) (Z H : ℝ) (w : ℕ → ℝ),
      2 ≤ Z → ⌊Z⌋₊ ≤ Y → A ⊆ Finset.Ioc N (N + Y) →
      (∀ n ∈ A, ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤ Z ∧ d ∣ n ∧
        w n ≤ Real.exp H * (d.divisors.card : ℝ) ^ r) →
      (∑ n ∈ A, w n) ≤
        2 * (Y : ℝ) * Real.exp (H + C * Real.log (1 + Real.log Z)) := by
  obtain ⟨C, hC, hharm⟩ := harmonic_divisor_moment_real_cutoff r
  refine ⟨C, hC, ?_⟩
  intro N Y A Z H w hZ hZY hA hprefix
  have hbase := sum_le_divisor_majorant N Y A (Finset.Icc 1 ⌊Z⌋₊) w
    (fun d => Real.exp H * (d.divisors.card : ℝ) ^ r) hA (by
      intro n hn
      obtain ⟨d, hd0, hdZ, hdn, hdw⟩ := hprefix n hn
      exact ⟨d, Finset.mem_Icc.mpr ⟨hd0, Nat.le_floor hdZ⟩, hdn, hdw⟩)
    (by intro d hd; positivity) (by
      intro d hd
      obtain ⟨hd0, hdZ⟩ := Finset.mem_Icc.mp hd
      refine ⟨hd0, ?_⟩
      exact hdZ.trans hZY)
  calc
    (∑ n ∈ A, w n) ≤ 2 * (Y : ℝ) *
        ∑ d ∈ Finset.Icc 1 ⌊Z⌋₊, (Real.exp H * (d.divisors.card : ℝ) ^ r) / d := hbase
    _ = 2 * (Y : ℝ) * (Real.exp H *
        ∑ d ∈ Finset.Icc 1 ⌊Z⌋₊, (d.divisors.card : ℝ) ^ r / d) := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ ≤ 2 * (Y : ℝ) * (Real.exp H *
        Real.exp (C * Real.log (1 + Real.log Z))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hharm Z hZ) (Real.exp_pos H).le) (by positivity)
    _ = 2 * (Y : ℝ) * Real.exp (H + C * Real.log (1 + Real.log Z)) := by
      rw [Real.exp_add]

/-- The same estimate indexed by the positive translation parameter h. -/
theorem shifted_harmonic_prefix_budget (r : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N Y : ℕ) (A : Finset ℕ) (Z H : ℝ) (w : ℕ → ℝ),
      2 ≤ Z → ⌊Z⌋₊ ≤ Y → A ⊆ Finset.Icc 1 Y →
      (∀ h ∈ A, ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤ Z ∧ d ∣ N + h ∧
        w h ≤ Real.exp H * (d.divisors.card : ℝ) ^ r) →
      (∑ h ∈ A, w h) ≤
        2 * (Y : ℝ) * Real.exp (H + C * Real.log (1 + Real.log Z)) := by
  obtain ⟨C, hC, hbudget⟩ := harmonic_prefix_budget r
  refine ⟨C, hC, ?_⟩
  intro N Y A Z H w hZ hZY hA hprefix
  have h := hbudget N Y (A.image (fun h => N + h)) Z H
    (fun n => w (n - N)) hZ hZY (by
      intro n hn
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hn
      have haI := Finset.mem_Icc.mp (hA ha)
      exact Finset.mem_Ioc.mpr (by omega)) (by
      intro n hn
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hn
      simpa only [Nat.add_sub_cancel_left] using hprefix a ha)
  rw [Finset.sum_image] at h
  · simpa only [Nat.add_sub_cancel_left] using h
  · intro a ha b hb hab
    exact Nat.add_left_cancel hab

/-- The shifted prefix budget with the manuscript's real-valued interval length. -/
theorem real_shifted_harmonic_prefix_budget (r : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (Y : ℝ) (A : Finset ℕ) (Z H : ℝ) (w : ℕ → ℝ),
      2 ≤ Z → Z ≤ Y → A ⊆ Finset.Icc 1 ⌊Y⌋₊ →
      (∀ h ∈ A, ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤ Z ∧ d ∣ N + h ∧
        w h ≤ Real.exp H * (d.divisors.card : ℝ) ^ r) →
      (∑ h ∈ A, w h) ≤
        2 * Y * Real.exp (H + C * Real.log (1 + Real.log Z)) := by
  obtain ⟨C, hC, hbudget⟩ := shifted_harmonic_prefix_budget r
  refine ⟨C, hC, ?_⟩
  intro N Y A Z H w hZ hZY hA hprefix
  apply (hbudget N ⌊Y⌋₊ A Z H w hZ (Nat.floor_mono hZY) hA hprefix).trans
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  exact mul_le_mul_of_nonneg_left (Nat.floor_le (by linarith : 0 ≤ Y)) (by norm_num)

end Problem337.DivisorMoment

end

end OAI
