import OAI.NumberTheory.TwoPointCorrelations.MRTBinPrefactor

namespace OAI

/-! The later frequency classes have a summable bound, with the true
resolution and all witness-bin choices included. -/

namespace TwoPointCorrelations

open Finset

lemma mrt_later_bin_prefactor_saving {η P Q : ℝ} (hη : 0 < η) (hη' : η ≤ 1 / 6)
    (k : ℕ) (hk : 2 ≤ k) (hP0 : 0 < P) (hP : 2 ≤ Real.log P) (hQ : 1 ≤ Real.log Q)
    (hPQ : Real.log P ≤ Real.log Q)
    (hbudget : 8192 * (Real.log (Real.log Q) + 1) ≤ η * Real.log P) :
    (64 * Real.exp 11 *
        (mrtResolution P Q η (k - 1) * Real.log (mrtBandUpper Q (k - 1)) + 1) *
        (mrtResolution P Q η k * Real.log (mrtBandUpper Q k) + 1) *
        (mrtResolution P Q η k / (η / (2 * (k : ℝ) ^ 2)))) *
        (mrtBandLower P Q k) ^ (-(η / (2 * (k : ℝ) ^ 2))) ≤
      P⁻¹ * ((k : ℝ) ^ 2)⁻¹ := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hy : 1 ≤ Real.log (Real.log Q) + 1 := by linarith [Real.log_nonneg hQ]
  have hηQ : 8192 ≤ η * Real.log Q := by
    have hh := mul_le_mul_of_nonneg_left hPQ hη.le
    nlinarith
  have hlarge := mrt_later_band_exponential_budget (P := P) (Q := Q) hη.le k hk
    (by linarith) hQ hηQ
  have hkpow : (k : ℝ) ^ 2 ≤ (k : ℝ) ^ 6 := pow_le_pow_right₀ hk1 (by norm_num)
  have hkp : (k : ℝ) ≤ (k : ℝ) ^ 2 * Real.log P := by
    have hh : (k : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
    nlinarith
  have hpp : Real.log P ≤ (k : ℝ) ^ 2 * Real.log P := by
    have hh : 1 ≤ (k : ℝ) ^ 2 := one_le_pow₀ hk1
    nlinarith
  have hlogk : Real.log (k : ℝ) ≤ k :=
    (Real.log_le_sub_one_of_pos hk0).trans (by linarith)
  have hsave : 1024 * (k : ℝ) ^ 2 * Real.log P + Real.log P + 2 * Real.log (k : ℝ) ≤
      η * Real.log (mrtBandLower P Q k) / (2 * (k : ℝ) ^ 2) := by
    have hh := mul_le_mul_of_nonneg_right hkpow (by linarith : 0 ≤ Real.log P)
    have he : η * Real.log (mrtBandLower P Q k) / (2 * (k : ℝ) ^ 2) =
        2 * (η * Real.log (mrtBandLower P Q k) / (4 * (k : ℝ) ^ 2)) := by ring
    rw [he]
    nlinarith
  have hL0 : 0 < mrtBandLower P Q k := Real.exp_pos _
  calc
    _ ≤ Real.exp (1024 * (k : ℝ) ^ 2 * Real.log P) *
        (mrtBandLower P Q k) ^ (-(η / (2 * (k : ℝ) ^ 2))) :=
      mul_le_mul_of_nonneg_right (mrt_actual_bin_prefactor hη hη' k hk hP0 hP hQ hbudget)
        (Real.rpow_nonneg hL0.le _)
    _ = Real.exp (1024 * (k : ℝ) ^ 2 * Real.log P -
        η * Real.log (mrtBandLower P Q k) / (2 * (k : ℝ) ^ 2)) := by
      rw [Real.rpow_def_of_pos hL0, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-Real.log P - 2 * Real.log (k : ℝ)) :=
      Real.exp_le_exp.mpr (by linarith)
    _ = P⁻¹ * ((k : ℝ) ^ 2)⁻¹ := by
      rw [Real.exp_sub, Real.exp_neg, Real.exp_log hP0,
        show Real.exp (2 * Real.log (k : ℝ)) = (Real.exp (Real.log (k : ℝ))) ^ 2 by
          simpa using Real.exp_nat_mul (Real.log (k : ℝ)) 2,
        Real.exp_log hk0]
      ring

theorem mrt_later_bin_moment_sum {η P Q τ : ℝ}
    (hη : 0 < η) (hη' : η ≤ 1 / 6) (j : ℕ)
    (hP0 : 0 < P) (hP : 2 ≤ Real.log P) (hQ : 1 ≤ Real.log Q)
    (hPQ : Real.log P ≤ Real.log Q)
    (hbudget : 8192 * (Real.log (Real.log Q) + 1) ≤ η * Real.log P)
    (hH : 2 ≤ mrtBaseResolution P Q η) (hτ : 0 ≤ τ) :
    2 * ∑ b ∈ mrtLogBins (mrtResolution P Q η (j + 1))
        (mrtBandLower P Q (j + 1)) (mrtBandUpper Q (j + 1)),
      ((mrtLogBins (mrtResolution P Q η (j + 2))
        (mrtBandLower P Q (j + 2)) (mrtBandUpper Q (j + 2))).card : ℝ) *
      ∑ k ∈ mrtLogBins (mrtResolution P Q η (j + 2))
        (mrtBandLower P Q (j + 2)) (mrtBandUpper Q (j + 2)),
        mrtMixedBinCost η j τ
          (mrtPrimeLogLower (mrtResolution P Q η (j + 1)) b)
          (mrtPrimeLogLower (mrtResolution P Q η (j + 2)) k) ≤
      (τ + 1) * P⁻¹ * (((j : ℝ) + 2) ^ 2)⁻¹ := by
  have hresolution (k : ℕ) (hk : 1 ≤ k) : 2 ≤ mrtResolution P Q η k := by
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hpow : 1 ≤ (k : ℝ) ^ 2 := one_le_pow₀ hk1
    dsimp [mrtResolution]
    nlinarith [mrtBaseResolution_pos P Q η]
  have hh := mrt_actual_bin_moment_sum hη hη' j hP hQ hbudget
    (hresolution (j + 1) (by omega)) (hresolution (j + 2) (by omega)) hτ
  apply hh.trans
  have hs := mul_le_mul_of_nonneg_left
    (mrt_later_bin_prefactor_saving hη hη' (j + 2) (by omega) hP0 hP hQ hPQ hbudget)
    (show 0 ≤ τ + 1 by linarith)
  have hj : j + 2 - 1 = j + 1 := by omega
  simp only [hj, Nat.cast_add, Nat.cast_ofNat] at hs
  convert hs using 1 <;> ring

end TwoPointCorrelations

end OAI
