import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTBinMomentSum
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTResolution

namespace OAI

/-! The first small-prime frequency class has exactly the reciprocal
resolution saving dictated by the cubic balance. -/

namespace TwoPointCorrelations

open Finset

theorem mrt_first_bin_moment_sum {η P Q N T : ℝ}
    (hη : 0 ≤ η) (hη' : η ≤ 1 / 12) (hP : 1 ≤ P) (hQ0 : 0 < Q) (hQ : 1 ≤ Real.log Q)
    (hH : 2 ≤ mrtBaseResolution P Q η) (hN : 0 < N) (hT : 0 ≤ T) :
    64 * Real.exp 1 * ((mrtLogBins (mrtBaseResolution P Q η) P Q).card : ℝ) *
        ∑ k ∈ mrtLogBins (mrtBaseResolution P Q η) P Q,
          (Real.exp (-mrtFrequencyExponent η 0 *
              Real.log (mrtPrimeLogLower (mrtBaseResolution P Q η) k))) ^ 2 *
            (T * mrtPrimeLogLower (mrtBaseResolution P Q η) k / N + 1) ≤
      1024 * Real.exp 2 * (T * Q / N + 1) * (mrtBaseResolution P Q η)⁻¹ := by
  let H := mrtBaseResolution P Q η
  let β := 2 * mrtFrequencyExponent η 0
  have hβ : 1 / 4 ≤ β := by
    dsimp [β]
    rw [mrtFrequencyExponent_zero]
    linarith
  have hβ' : β ≤ 1 / 2 := by
    dsimp [β]
    rw [mrtFrequencyExponent_zero]
    linarith
  have hH0 : 0 < H := mrtBaseResolution_pos P Q η
  have hQ1 : 1 < Q := by
    have hh : 1 < Real.exp (Real.log Q) := Real.one_lt_exp_iff.mpr (by linarith)
    simpa only [Real.exp_log hQ0] using hh
  have he (k : ℕ) :
      (Real.exp (-mrtFrequencyExponent η 0 * Real.log (mrtPrimeLogLower H k))) ^ 2 =
        Real.exp (-β * (k : ℝ) / H) := by
    rw [← Real.exp_nat_mul]
    simp only [mrtPrimeLogLower, Real.log_exp]
    dsimp [β]
    congr 1
    ring
  dsimp only [H] at he
  simp_rw [he]
  have hs := mrt_log_bin_weighted_sum (by linarith : 0 < β) hH0
    (by dsimp [H]; linarith : β ≤ H) hP hQ1.le hN hT
  have hc := mrt_log_bin_card (P := P) hH0.le hQ1.le
  have hc' : ((mrtLogBins H P Q).card : ℝ) ≤ 2 * H * Real.log Q := by
    have hh : 1 ≤ H * Real.log Q := by dsimp [H]; nlinarith
    change ((Icc ⌊H * Real.log P⌋₊ ⌊H * Real.log Q⌋₊).card : ℝ) ≤ _
    linarith
  have hi : 1 / β ≤ 4 := (div_le_iff₀ (by linarith : 0 < β)).mpr (by linarith)
  have hbalance : H ^ 2 * Real.log Q * P ^ (-β) = H⁻¹ := by
    rw [Real.rpow_def_of_pos (by linarith : 0 < P)]
    dsimp [β, H]
    rw [show Real.log P * -(2 * mrtFrequencyExponent η 0) =
      -2 * mrtFrequencyExponent η 0 * Real.log P by ring]
    exact mrt_base_resolution_first_cost P Q η hQ1
  calc
    _ ≤ 64 * Real.exp 1 * (2 * H * Real.log Q) *
        (((2 * Real.exp 1 * H / β) * P ^ (-β)) * (T * Q / N + 1)) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hc' (by positivity)
      · exact hs
      · exact sum_nonneg (fun _ _ => mul_nonneg (Real.exp_pos _).le
          (by unfold mrtPrimeLogLower; positivity))
      · positivity
    _ = 256 * Real.exp 2 * (T * Q / N + 1) *
        (H ^ 2 * Real.log Q * P ^ (-β)) * (1 / β) := by
      rw [show Real.exp 2 = Real.exp 1 * Real.exp 1 by rw [← Real.exp_add]; norm_num]
      ring
    _ ≤ 256 * Real.exp 2 * (T * Q / N + 1) * H⁻¹ * 4 := by
      rw [hbalance]
      exact mul_le_mul_of_nonneg_left hi (by positivity)
    _ = _ := by dsimp [H]; ring

end TwoPointCorrelations

end OAI
