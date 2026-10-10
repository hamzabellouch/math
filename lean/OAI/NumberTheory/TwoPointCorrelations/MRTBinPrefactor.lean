import OAI.NumberTheory.TwoPointCorrelations.MRTResolution
import OAI.NumberTheory.TwoPointCorrelations.MRTBandPowerSaving
import OAI.NumberTheory.TwoPointCorrelations.MRTBinMomentSum

namespace OAI

/-! Explicit polynomial factors in the later-band estimate are absorbed
by a small part of the saving from the true band endpoints. -/

namespace TwoPointCorrelations

lemma mrt_log_band_upper_mono {Q : ℝ} (hQ : 1 ≤ Real.log Q)
    {i k : ℕ} (hi : 1 ≤ i) (hik : i ≤ k) :
    Real.log (mrtBandUpper Q i) ≤ Real.log (mrtBandUpper Q k) := by
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg _
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (hi.trans hik)
  have hik' : (i : ℝ) ≤ k := by exact_mod_cast hik
  simp only [mrtBandUpper, Real.log_exp]
  apply mul_le_mul
  · exact (pow_le_pow_left₀ hi0 hik' _).trans
      (pow_le_pow_right₀ hk1 (by omega))
  · exact pow_le_pow_right₀ hQ hik
  · positivity
  · positivity

lemma mrt_bin_prefactor_exponential {P L η k : ℝ}
    (hk : 2 ≤ k) (hP0 : 0 < P) (hP : 2 ≤ Real.log P) (hL : 1 ≤ L) (hη : 0 < η)
    (hlogL : Real.log L ≤ 8 * k ^ 2 * Real.log P)
    (hinv : η⁻¹ ≤ Real.log P) :
    512 * Real.exp 11 * k ^ 8 * P ^ 3 * L ^ 2 / η ≤
      Real.exp (1024 * k ^ 2 * Real.log P) := by
  have hk0 : 0 ≤ k := by linarith
  have hc : (512 : ℝ) ≤ Real.exp 512 := by
    linarith [Real.add_one_le_exp (512 : ℝ)]
  have hkexp : k ^ 8 ≤ Real.exp (8 * k) := by
    have hh : k ≤ Real.exp k := by linarith [Real.add_one_le_exp k]
    exact (pow_le_pow_left₀ hk0 hh 8).trans_eq (Real.exp_nat_mul k 8).symm
  have hpexp : P ^ 3 = Real.exp (3 * Real.log P) := by
    rw [show Real.exp (3 * Real.log P) = (Real.exp (Real.log P)) ^ 3 by
      simpa using Real.exp_nat_mul (Real.log P) 3, Real.exp_log hP0]
  have hLexp : L ^ 2 ≤ Real.exp (16 * k ^ 2 * Real.log P) := by
    calc
      L ^ 2 = Real.exp (2 * Real.log L) := by
        rw [show Real.exp (2 * Real.log L) = (Real.exp (Real.log L)) ^ 2 by
          simpa using Real.exp_nat_mul (Real.log L) 2, Real.exp_log (by linarith : 0 < L)]
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  have hPexp := hpexp.le
  have hηexp : η⁻¹ ≤ Real.exp (Real.log P) :=
    hinv.trans (by linarith [Real.add_one_le_exp (Real.log P)])
  have hk2 : k ≤ k ^ 2 := by nlinarith
  have hk2p : k ≤ k ^ 2 * Real.log P := by nlinarith
  have hpp : Real.log P ≤ k ^ 2 * Real.log P := by
    nlinarith [mul_nonneg (show 0 ≤ k ^ 2 - 1 by nlinarith) (by linarith : 0 ≤ Real.log P)]
  have hbase : 8 ≤ k ^ 2 * Real.log P := by
    nlinarith [mul_nonneg (show 0 ≤ k ^ 2 - 4 by nlinarith) (by linarith : 0 ≤ Real.log P - 2)]
  calc
    _ = 512 * Real.exp 11 * k ^ 8 * P ^ 3 * L ^ 2 * η⁻¹ := by ring
    _ ≤ Real.exp 512 * Real.exp 11 * Real.exp (8 * k) *
        Real.exp (3 * Real.log P) * Real.exp (16 * k ^ 2 * Real.log P) *
        Real.exp (Real.log P) := by gcongr
    _ = Real.exp (523 + 8 * k + 4 * Real.log P + 16 * k ^ 2 * Real.log P) := by
      simp only [← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

theorem mrt_actual_bin_prefactor {η P Q : ℝ} (hη : 0 < η) (hη' : η ≤ 1 / 6)
    (k : ℕ) (hk : 2 ≤ k) (hP0 : 0 < P) (hP : 2 ≤ Real.log P) (hQ : 1 ≤ Real.log Q)
    (hbudget : 8192 * (Real.log (Real.log Q) + 1) ≤ η * Real.log P) :
    64 * Real.exp 11 *
        (mrtResolution P Q η (k - 1) * Real.log (mrtBandUpper Q (k - 1)) + 1) *
        (mrtResolution P Q η k * Real.log (mrtBandUpper Q k) + 1) *
        (mrtResolution P Q η k / (η / (2 * (k : ℝ) ^ 2))) ≤
      Real.exp (1024 * (k : ℝ) ^ 2 * Real.log P) := by
  have hk1 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hP1 : 1 ≤ P := (Real.one_lt_exp_iff.mpr (by linarith : 0 < Real.log P)).le.trans_eq
    (Real.exp_log hP0)
  have hy : 1 ≤ Real.log (Real.log Q) + 1 := by linarith [Real.log_nonneg hQ]
  have hpη : 1 ≤ η * Real.log P := by nlinarith
  have hinv : η⁻¹ ≤ Real.log P := by
    rw [← one_div, div_le_iff₀ hη]
    nlinarith
  have hyP : Real.log (Real.log Q) + 1 ≤ Real.log P := by
    nlinarith [mul_le_mul_of_nonneg_right hη' (by linarith : 0 ≤ Real.log P)]
  have hL : 1 ≤ Real.log (mrtBandUpper Q k) :=
    (show (1 : ℝ) ≤ k by exact_mod_cast (show 1 ≤ k by omega)).trans
      (mrt_band_index_le_log_upper Q k (by omega) hQ)
  have hlogL : Real.log (Real.log (mrtBandUpper Q k)) ≤
      8 * (k : ℝ) ^ 2 * Real.log P := by
    have hh := mrt_log_log_band_upper Q k (by omega) hQ
    have hh' := mul_le_mul_of_nonneg_left hyP (show 0 ≤ 8 * (k : ℝ) ^ 2 by positivity)
    linarith
  have hH₁ := mrt_resolution_le hP1 hQ hη.le k
  have hH₀ : mrtResolution P Q η (k - 1) ≤ (k : ℝ) ^ 2 * P := by
    apply (mrt_resolution_le hP1 hQ hη.le (k - 1)).trans
    gcongr
    exact_mod_cast Nat.sub_le k 1
  have hU := mrt_log_band_upper_mono hQ (show 1 ≤ k - 1 by omega) (Nat.sub_le k 1)
  have hH₀0 : 0 ≤ mrtResolution P Q η (k - 1) := (mrtResolution_pos P Q η (by omega)).le
  have hH₁0 : 0 ≤ mrtResolution P Q η k := (mrtResolution_pos P Q η (by omega)).le
  have hU₀0 : 0 ≤ Real.log (mrtBandUpper Q (k - 1)) := by
    have hh := mrt_band_index_le_log_upper Q (k - 1) (by omega) hQ
    exact (Nat.cast_nonneg _).trans hh
  have hB : 1 ≤ (k : ℝ) ^ 2 * P * Real.log (mrtBandUpper Q k) :=
    one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (by nlinarith) hP1) hL
  have hF₀ : mrtResolution P Q η (k - 1) * Real.log (mrtBandUpper Q (k - 1)) + 1 ≤
      2 * (k : ℝ) ^ 2 * P * Real.log (mrtBandUpper Q k) := by
    have hh := mul_le_mul hH₀ hU hU₀0 (by positivity : 0 ≤ (k : ℝ) ^ 2 * P)
    nlinarith
  have hF₁ : mrtResolution P Q η k * Real.log (mrtBandUpper Q k) + 1 ≤
      2 * (k : ℝ) ^ 2 * P * Real.log (mrtBandUpper Q k) := by
    have hh := mul_le_mul_of_nonneg_right hH₁ (by linarith : 0 ≤ Real.log (mrtBandUpper Q k))
    nlinarith
  calc
    _ ≤ 64 * Real.exp 11 *
        (2 * (k : ℝ) ^ 2 * P * Real.log (mrtBandUpper Q k)) *
        (2 * (k : ℝ) ^ 2 * P * Real.log (mrtBandUpper Q k)) *
        (((k : ℝ) ^ 2 * P) / (η / (2 * (k : ℝ) ^ 2))) := by gcongr
    _ = 512 * Real.exp 11 * (k : ℝ) ^ 8 * P ^ 3 *
        Real.log (mrtBandUpper Q k) ^ 2 / η := by field_simp; ring
    _ ≤ _ := mrt_bin_prefactor_exponential hk1 hP0 hP hL hη hlogL hinv

end TwoPointCorrelations

end OAI
