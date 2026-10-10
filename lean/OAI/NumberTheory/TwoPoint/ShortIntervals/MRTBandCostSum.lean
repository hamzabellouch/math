import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTBandMixedBound
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTLogBinEndpoints

namespace OAI

/-! Summing the actual amplified cofactor cost over the preceding
witness bins and current small-polynomial bins. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def mrtMixedBinCost (η : ℝ) (j : ℕ) (τ Y u : ℝ) : ℝ :=
  Real.exp (-mrtFrequencyExponent η (j + 1) * Real.log u) ^ 2 *
    ((16 * Real.exp 10 *
      (τ + (2 : ℝ) ^ (mrtAmplificationOrder ⌈Y⌉₊ u + 1) * ⌈Y⌉₊) *
        ((mrtAmplificationOrder ⌈Y⌉₊ u).factorial : ℝ) ^ 2) /
      Real.exp (-mrtFrequencyExponent η j * Real.log Y) ^
        (2 * mrtAmplificationOrder ⌈Y⌉₊ u))

lemma mrt_mixed_bin_cost_bound {η P Q Y u τ : ℝ}
    (hη : 0 ≤ η) (hη' : η ≤ 1 / 6) (j : ℕ)
    (hP : 2 ≤ Real.log P) (hQ : 1 ≤ Real.log Q)
    (hbudget : 8192 * (Real.log (Real.log Q) + 1) ≤ η * Real.log P)
    (hYlo : Real.exp (-1) * mrtBandLower P Q (j + 1) ≤ Y)
    (hYhi : Y ≤ mrtBandUpper Q (j + 1))
    (hulo : Real.exp (-1) * mrtBandLower P Q (j + 2) ≤ u)
    (huhi : u ≤ mrtBandUpper Q (j + 2)) (hτ : 0 ≤ τ) :
    mrtMixedBinCost η j τ Y u ≤ 16 * Real.exp 10 * (τ + 1) *
      Real.exp (-η * Real.log u / (2 * ((j : ℝ) + 2) ^ 2)) := by
  have he : Real.exp (-mrtFrequencyExponent η (j + 1) * Real.log u) ^ 2 =
      Real.exp (-2 * mrtFrequencyExponent η (j + 1) * Real.log u) := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  have hb := mul_le_mul_of_nonneg_left
    (mrt_actual_band_mixed_bound hη hη' j hP hQ hbudget hYlo hYhi hulo huhi hτ)
    (show 0 ≤ 16 * Real.exp 10 by positivity)
  unfold mrtMixedBinCost
  rw [he]
  convert hb using 1 <;> ring

theorem mrt_mixed_bin_cost_sum {β κ : Type*} (B : Finset β) (K : Finset κ)
    (Y : β → ℝ) (u : κ → ℝ) {η P Q τ : ℝ}
    (hη : 0 ≤ η) (hη' : η ≤ 1 / 6) (j : ℕ)
    (hP : 2 ≤ Real.log P) (hQ : 1 ≤ Real.log Q)
    (hbudget : 8192 * (Real.log (Real.log Q) + 1) ≤ η * Real.log P)
    (hY : ∀ b ∈ B, Real.exp (-1) * mrtBandLower P Q (j + 1) ≤ Y b ∧
      Y b ≤ mrtBandUpper Q (j + 1))
    (hu : ∀ k ∈ K, Real.exp (-1) * mrtBandLower P Q (j + 2) ≤ u k ∧
      u k ≤ mrtBandUpper Q (j + 2)) (hτ : 0 ≤ τ) :
    2 * ∑ b ∈ B, (K.card : ℝ) * ∑ k ∈ K, mrtMixedBinCost η j τ (Y b) (u k) ≤
      32 * Real.exp 10 * (τ + 1) * B.card * K.card *
        ∑ k ∈ K, Real.exp (-η * Real.log (u k) / (2 * ((j : ℝ) + 2) ^ 2)) := by
  have hb (b : β) (hmem : b ∈ B) :
      (K.card : ℝ) * ∑ k ∈ K, mrtMixedBinCost η j τ (Y b) (u k) ≤
      (K.card : ℝ) * (16 * Real.exp 10 * (τ + 1) *
        ∑ k ∈ K, Real.exp (-η * Real.log (u k) / (2 * ((j : ℝ) + 2) ^ 2))) := by
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    rw [mul_sum]
    apply sum_le_sum
    intro k hk
    exact mrt_mixed_bin_cost_bound hη hη' j hP hQ hbudget
      (hY b hmem).1 (hY b hmem).2 (hu k hk).1 (hu k hk).2 hτ
  calc
    _ ≤ 2 * ∑ b ∈ B, (K.card : ℝ) * (16 * Real.exp 10 * (τ + 1) *
        ∑ k ∈ K, Real.exp (-η * Real.log (u k) / (2 * ((j : ℝ) + 2) ^ 2))) :=
      mul_le_mul_of_nonneg_left (sum_le_sum hb) (by norm_num)
    _ = _ := by rw [sum_const, nsmul_eq_mul]; ring

end TwoPointCorrelations

end OAI
