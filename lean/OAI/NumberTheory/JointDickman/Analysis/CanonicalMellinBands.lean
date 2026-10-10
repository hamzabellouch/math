import OAI.NumberTheory.JointDickman.Analysis.MultiscaleMellinEnergy
import OAI.NumberTheory.TwoPointCorrelations.MRTFirstBinSum
import OAI.NumberTheory.TwoPointCorrelations.MRTLaterBinSum
import OAI.NumberTheory.TwoPointCorrelations.MRTBandSeparation

namespace OAI

/-! # The published logarithmic prime bands in the actual energy partition -/
namespace JointDickman
open Finset TwoPointCorrelations

noncomputable def canonicalMellinBands (P Q η : ℝ) : MellinPrimeBands where
  primes j := mrtPrimeBand (mrtBandLower P Q (j+1)) (mrtBandUpper Q (j+1))
  bins j := mrtLogBins (mrtResolution P Q η (j+1))
    (mrtBandLower P Q (j+1)) (mrtBandUpper Q (j+1))
  bin j := mrtPrimeLogBin (mrtResolution P Q η (j+1))
  lower j := mrtPrimeLogLower (mrtResolution P Q η (j+1))
  resolution j := Real.exp (1 / mrtResolution P Q η (j+1))
  threshold j k := Real.exp (-mrtFrequencyExponent η j *
    Real.log (mrtPrimeLogLower (mrtResolution P Q η (j+1)) k))

lemma canonical_resolution_ge_two {P Q η : ℝ}
    (hH : 2 ≤ mrtBaseResolution P Q η) (j : ℕ) :
    2 ≤ mrtResolution P Q η (j+1) := by
  have hj : (1 : ℝ) ≤ (j+1 : ℕ) := by exact_mod_cast (show 1 ≤ j+1 by omega)
  have hp := one_le_pow₀ (n := 2) hj
  unfold mrtResolution
  nlinarith [mrtBaseResolution_pos P Q η]

lemma canonical_band_lower_ge {P Q : ℝ} (hP : 2 ≤ P) (hPQ : P ≤ Q)
    (hlogP : 1 < Real.log P) (j : ℕ) : P ≤ mrtBandLower P Q (j+1) := by
  have hh := mrt_band_lower_monotone P Q 1 (j+1) (by omega) (by omega) hP hPQ hlogP
  simpa only [mrtBandLower_one P Q (by linarith)] using hh

/-- The entire finite family satisfies the geometric hypotheses of the
proved Ramaré partition as soon as its upper endpoints lie below `N/2`. -/
theorem canonicalMellinBands_valid {P Q η : ℝ} {J N : ℕ}
    (hP : 2 * Real.exp 1 ≤ P) (hPQ : P ≤ Q)
    (hlogP : 1 < Real.log P) (hH : 2 ≤ mrtBaseResolution P Q η)
    (hN : ∀ j ∈ range J, 2 * mrtBandUpper Q (j+1) ≤ N) :
    (canonicalMellinBands P Q η).Valid J N := by
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hP2 : 2 ≤ P := by nlinarith
  have hP0 : 0 < P := by linarith
  have hlogQ : 1 ≤ Real.log Q :=
    hlogP.le.trans (Real.log_le_log hP0 hPQ)
  have hHj (j : ℕ) := canonical_resolution_ge_two hH j
  have hL (j : ℕ) := canonical_band_lower_ge hP2 hPQ hlogP j
  have hU (j : ℕ) : 1 ≤ mrtBandUpper Q (j+1) :=
    (show 1 ≤ (2:ℝ) by norm_num).trans
      ((mrt_band_endpoints P Q (j+1) (by omega) hP2 hPQ hlogQ).1.trans
        (mrt_band_endpoints P Q (j+1) (by omega) hP2 hPQ hlogQ).2)
  constructor
  · intro j _ p hp
    exact mrtPrimeBand_prime hp
  · intro i hi j hj hij
    apply disjoint_left.mpr
    intro p hpi hpj
    have hip := mrtPrimeBand_bounds (Real.exp_pos _).le (Real.exp_pos _).le hpi
    have hjp := mrtPrimeBand_bounds (Real.exp_pos _).le (Real.exp_pos _).le hpj
    change mrtBandLower P Q (i+1) < (p : ℝ) ∧ (p : ℝ) ≤ mrtBandUpper Q (i+1) at hip
    change mrtBandLower P Q (j+1) < (p : ℝ) ∧ (p : ℝ) ≤ mrtBandUpper Q (j+1) at hjp
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have hh := mrt_band_gap P Q (i+1) (j+1) (by omega) (by omega) hP2 hPQ hlogP
      linarith
    · have hh := mrt_band_gap P Q (j+1) (i+1) (by omega) (by omega) hP2 hPQ hlogP
      linarith
  · intro j _ p hp
    have hb := mrtPrimeBand_bounds (Real.exp_pos _).le (Real.exp_pos _).le hp
    exact mrt_prime_log_bin_range (by linarith [hHj j]) (Real.exp_pos _) hb.1.le hb.2
  · intro j _
    exact (mrt_prime_log_width (hHj j)).1
  · intro j _
    exact (mrt_prime_log_width (hHj j)).2.1
  · intro j _ p hp
    exact mrt_prime_log_bin_bounds (by linarith [hHj j]) (mrtPrimeBand_prime hp).one_le
  · intro j _ k hk
    have hh := mrt_log_bin_lower_endpoint (by linarith [hHj j])
      (Real.exp_pos ((j+1 : ℕ) ^ (4*(j+1)) * Real.log Q ^ j * Real.log P))
      (mem_Icc.mp hk).1
    have heq : Real.exp (-1) * (2 * Real.exp 1) = 2 := by
      rw [mul_left_comm, ← Real.exp_add]
      norm_num
    calc
      2 = Real.exp (-1) * (2 * Real.exp 1) := heq.symm
      _ ≤ Real.exp (-1) * mrtBandLower P Q (j+1) :=
        mul_le_mul_of_nonneg_left (hP.trans (hL j)) (Real.exp_pos _).le
      _ ≤ _ := hh
  · intro j hj k hk
    have hh := mrt_prime_log_lower_le_upper (by linarith [hHj j]) (hU j) (mem_Icc.mp hk).2
    apply (le_div_iff₀ (Real.exp_pos _)).mpr
    exact (mul_le_mul_of_nonneg_left hh (by norm_num)).trans (hN j hj)
  · intro j _ k _
    exact Real.exp_pos _

theorem canonical_initialCost_le {P Q η : ℝ} (N : ℕ) {T : ℝ}
    (hη : 0 ≤ η) (hη' : η ≤ 1/12) (hP : 1 ≤ P) (hQ0 : 0 < Q)
    (hQ : 1 ≤ Real.log Q) (hH : 2 ≤ mrtBaseResolution P Q η)
    (hN : 0 < (N : ℝ)) (hT : 0 ≤ T) :
    (canonicalMellinBands P Q η).initialCost N T ≤
      1024 * Real.exp 2 * (T * Q / N + 1) * (mrtBaseResolution P Q η)⁻¹ := by
  simpa only [MellinPrimeBands.initialCost, canonicalMellinBands,
    Nat.zero_add, mrtResolution_one, mrtBandLower_one P Q (by linarith),
    mrtBandUpper_one Q hQ0] using mrt_first_bin_moment_sum hη hη' hP hQ0 hQ hH hN hT

lemma canonical_laterCost_eq (P Q η : ℝ) (j N : ℕ) (T : ℝ) :
    (canonicalMellinBands P Q η).laterCost (j+1) N T =
      2 * ∑ b ∈ mrtLogBins (mrtResolution P Q η (j+1))
        (mrtBandLower P Q (j+1)) (mrtBandUpper Q (j+1)),
      ((mrtLogBins (mrtResolution P Q η (j+2))
        (mrtBandLower P Q (j+2)) (mrtBandUpper Q (j+2))).card : ℝ) *
        ∑ k ∈ mrtLogBins (mrtResolution P Q η (j+2))
          (mrtBandLower P Q (j+2)) (mrtBandUpper Q (j+2)),
        mrtMixedBinCost η j (T / N)
          (mrtPrimeLogLower (mrtResolution P Q η (j+1)) b)
          (mrtPrimeLogLower (mrtResolution P Q η (j+2)) k) := by
  dsimp only [MellinPrimeBands.laterCost, canonicalMellinBands]
  simp only [Nat.add_sub_cancel, show j+1+1 = j+2 by omega]
  congr 1

theorem canonical_laterCost_le {P Q η : ℝ} (j N : ℕ) {T : ℝ}
    (hη : 0 < η) (hη' : η ≤ 1/6) (hP0 : 0 < P) (hP : 2 ≤ Real.log P)
    (hQ : 1 ≤ Real.log Q) (hPQ : Real.log P ≤ Real.log Q)
    (hbudget : 8192 * (Real.log (Real.log Q) + 1) ≤ η * Real.log P)
    (hH : 2 ≤ mrtBaseResolution P Q η) (hT : 0 ≤ T) :
    (canonicalMellinBands P Q η).laterCost (j+1) N T ≤
      (T / N + 1) * P⁻¹ * (((j : ℝ)+2)^2)⁻¹ := by
  rw [canonical_laterCost_eq]
  exact mrt_later_bin_moment_sum hη hη' j hP0 hP hQ hPQ hbudget hH
    (div_nonneg hT (Nat.cast_nonneg N))

end JointDickman

end OAI
