import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTBandCostSum

namespace OAI

/-! The complete finite witness-bin sum. Both bin cardinalities and the
remaining exponential sum are bounded using their actual endpoints. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def mrtLogBins (H P Q : ℝ) : Finset ℕ :=
  Icc ⌊H * Real.log P⌋₊ ⌊H * Real.log Q⌋₊

theorem mrt_actual_bin_moment_sum {η P Q τ H₀ H₁ : ℝ}
    (hη : 0 < η) (hη' : η ≤ 1 / 6) (j : ℕ)
    (hP : 2 ≤ Real.log P) (hQ : 1 ≤ Real.log Q)
    (hbudget : 8192 * (Real.log (Real.log Q) + 1) ≤ η * Real.log P)
    (hH₀ : 2 ≤ H₀) (hH₁ : 2 ≤ H₁) (hτ : 0 ≤ τ) :
    2 * ∑ b ∈ mrtLogBins H₀ (mrtBandLower P Q (j + 1)) (mrtBandUpper Q (j + 1)),
      ((mrtLogBins H₁ (mrtBandLower P Q (j + 2)) (mrtBandUpper Q (j + 2))).card : ℝ) *
        ∑ k ∈ mrtLogBins H₁ (mrtBandLower P Q (j + 2)) (mrtBandUpper Q (j + 2)),
          mrtMixedBinCost η j τ (mrtPrimeLogLower H₀ b) (mrtPrimeLogLower H₁ k) ≤
      64 * Real.exp 11 * (τ + 1) *
        (H₀ * Real.log (mrtBandUpper Q (j + 1)) + 1) *
        (H₁ * Real.log (mrtBandUpper Q (j + 2)) + 1) *
        (H₁ / (η / (2 * ((j : ℝ) + 2) ^ 2))) *
        (mrtBandLower P Q (j + 2)) ^ (-(η / (2 * ((j : ℝ) + 2) ^ 2))) := by
  let B := mrtLogBins H₀ (mrtBandLower P Q (j + 1)) (mrtBandUpper Q (j + 1))
  let K := mrtLogBins H₁ (mrtBandLower P Q (j + 2)) (mrtBandUpper Q (j + 2))
  let β : ℝ := η / (2 * ((j : ℝ) + 2) ^ 2)
  have hβ : 0 < β := by dsimp [β]; positivity
  have hβH : β ≤ H₁ := by
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hd : 1 ≤ 2 * ((j : ℝ) + 2) ^ 2 := by nlinarith [sq_nonneg (j : ℝ)]
    have hh := div_le_self hη.le hd
    dsimp [β]
    linarith
  have hUpper (k : ℕ) : 1 ≤ mrtBandUpper Q (k + 1) := by
    apply Real.one_le_exp
    have hk : (0 : ℝ) ≤ (k + 1 : ℕ) := Nat.cast_nonneg _
    exact mul_nonneg (pow_nonneg hk _) (pow_nonneg (by linarith : 0 ≤ Real.log Q) _)
  have hLower (k : ℕ) : 1 ≤ mrtBandLower P Q (k + 1) := by
    apply Real.one_le_exp
    positivity
  have hU₂ : 1 ≤ mrtBandUpper Q (j + 2) := by
    simpa only [Nat.add_assoc] using hUpper (j + 1)
  have hL₂ : 1 ≤ mrtBandLower P Q (j + 2) := by
    simpa only [Nat.add_assoc] using hLower (j + 1)
  have hcB := mrt_log_bin_card (P := mrtBandLower P Q (j + 1))
    (by linarith : 0 ≤ H₀) (hUpper j)
  have hcK := mrt_log_bin_card (P := mrtBandLower P Q (j + 2))
    (by linarith : 0 ≤ H₁) hU₂
  have hh := mrt_mixed_bin_cost_sum B K (mrtPrimeLogLower H₀) (mrtPrimeLogLower H₁)
    hη.le hη' j hP hQ hbudget
    (fun b hb => mrt_log_bin_endpoints (by linarith) (Real.exp_pos _) (hUpper j) hb)
    (fun k hk => mrt_log_bin_endpoints (by linarith) (Real.exp_pos _) hU₂ hk) hτ
  have hs := mrt_first_band_exponential_sum hβ (by linarith : 0 < H₁)
    hβH hL₂ ⌊H₁ * Real.log (mrtBandUpper Q (j + 2))⌋₊
  have he (k : ℕ) :
      -η * Real.log (mrtPrimeLogLower H₁ k) / (2 * ((j : ℝ) + 2) ^ 2) =
        -β * (k : ℝ) / H₁ := by
    simp only [mrtPrimeLogLower, Real.log_exp]
    dsimp [β]
    ring
  simp_rw [he] at hh
  apply hh.trans
  have hnB : 0 ≤ H₀ * Real.log (mrtBandUpper Q (j + 1)) + 1 :=
    (Nat.cast_nonneg B.card).trans hcB
  have hnK : 0 ≤ H₁ * Real.log (mrtBandUpper Q (j + 2)) + 1 :=
    (Nat.cast_nonneg K.card).trans hcK
  calc
    _ ≤ 32 * Real.exp 10 * (τ + 1) *
        (H₀ * Real.log (mrtBandUpper Q (j + 1)) + 1) *
        (H₁ * Real.log (mrtBandUpper Q (j + 2)) + 1) *
        ((2 * Real.exp 1 * H₁ / β) * (mrtBandLower P Q (j + 2)) ^ (-β)) := by
      apply mul_le_mul
      · apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hcB (by positivity)
        · exact hcK
        · exact Nat.cast_nonneg K.card
        · positivity
      · exact hs
      · exact sum_nonneg (fun _ _ => (Real.exp_pos _).le)
      · positivity
    _ = _ := by
      rw [show Real.exp 11 = Real.exp 10 * Real.exp 1 by rw [← Real.exp_add]; norm_num]
      dsimp [β]
      ring

end TwoPointCorrelations

end OAI
