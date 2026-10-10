import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTNoSmallCount
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTMaximalBand

namespace OAI

/-! Actual logarithmic-bin cardinality at the maximal-band cutoff.
The resolution is controlled by the original prime endpoint, so the
number of bins contributes only exp(o(log N)). -/

namespace TwoPointCorrelations

open Filter Finset

lemma mrt_final_bin_count_coarse {L P Q η : ℝ} (hL : 1 ≤ L)
    (hP : 1 ≤ P) (hPQ : P ≤ Q) (hQ : 1 ≤ Real.log Q) (hη : 0 ≤ η)
    (j : ℕ) (hupper : Real.log (mrtBandUpper Q (j+1)) ≤ Real.sqrt L) :
    ((mrtLogFamilyBins P Q η j).card:ℝ) ≤ L^2*Real.exp (Real.sqrt L)+1 := by
  have hL0 : 0 < L := by linarith
  have hP0 : 0 < P := by linarith
  have hj : (j+1:ℕ) ≥ 1 := by omega
  have hindex : ((j+1:ℕ):ℝ) ≤ Real.sqrt L :=
    (mrt_band_index_le_log_upper Q (j+1) hj hQ).trans hupper
  have hj2 : (((j+1:ℕ):ℝ))^2 ≤ L := by
    have hh := pow_le_pow_left₀ (Nat.cast_nonneg (j+1)) hindex 2
    simpa only [Real.sq_sqrt hL0.le] using hh
  have hlogQ : Real.log Q ≤ Real.sqrt L := by
    have hh := (mrt_band_upper_log_mono hQ (i := 1) (j := j+1) (by omega) (by omega)).trans hupper
    simpa [mrtBandUpper] using hh
  have hlogP : Real.log P ≤ Real.sqrt L :=
    (Real.log_le_log hP0 hPQ).trans hlogQ
  have hPupper : P ≤ Real.exp (Real.sqrt L) := by
    simpa only [Real.exp_log hP0] using Real.exp_le_exp.mpr hlogP
  have hH : mrtResolution P Q η (j+1) ≤ L*Real.exp (Real.sqrt L) :=
    (mrt_resolution_le hP hQ hη (j+1)).trans
      (mul_le_mul hj2 hPupper (by positivity) hL0.le)
  have hBU : 1 ≤ mrtBandUpper Q (j+1) := by
    have hq0 : 0 ≤ Real.log Q := by linarith
    unfold mrtBandUpper
    exact Real.one_le_exp (by positivity)
  have hH0 : 0 ≤ mrtResolution P Q η (j+1) :=
    (mrtResolution_pos P Q η hj).le
  have hcard := mrt_log_bin_card (P := mrtBandLower P Q (j+1)) hH0 hBU
  change ((mrtLogFamilyBins P Q η j).card:ℝ) ≤
    mrtResolution P Q η (j+1)*Real.log (mrtBandUpper Q (j+1))+1 at hcard
  apply hcard.trans
  have hroot := Real.sqrt_le_self_iff.mpr (Or.inr hL)
  have hbound := mul_le_mul hH (hupper.trans hroot)
    (Real.log_nonneg hBU) (by positivity)
  nlinarith

lemma mrt_eventually_bin_count_budget :
    ∀ᶠ L : ℝ in atTop, L^2*Real.exp (Real.sqrt L)+1 ≤
      Real.exp ((3/1000:ℝ)*L) := by
  have hb := (isLittleO_log_rpow_atTop (show (0:ℝ)<1 by norm_num)).bound
    (show (0:ℝ)<1/4000 by norm_num)
  filter_upwards [hb,eventually_ge_atTop (1000000:ℝ)] with L hb hL
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg hL1),Real.norm_eq_abs,
    Real.rpow_one,abs_of_pos hL0] at hb
  have hroot : Real.sqrt L ≤ L/1000 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    have hh := mul_nonneg (show 0 ≤ L-1000000 by linarith) hL0.le
    nlinarith
  have hlog2 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have he1 : 1 ≤ Real.exp (Real.sqrt L) := Real.one_le_exp (Real.sqrt_nonneg L)
  have hL2 : 1 ≤ L^2 := one_le_pow₀ hL1
  have hprod : 1 ≤ L^2*Real.exp (Real.sqrt L) :=
    one_le_mul_of_one_le_of_one_le hL2 he1
  have he : Real.exp (2*Real.log L)=L^2 := by
    simpa only [Nat.cast_ofNat,Real.exp_log hL0] using Real.exp_nat_mul (Real.log L) 2
  calc
    _ ≤ 2*L^2*Real.exp (Real.sqrt L) := by nlinarith
    _ = Real.exp (Real.log 2+2*Real.log L+Real.sqrt L) := by
      conv_rhs => rw [Real.exp_add,Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<2),he]
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

theorem mrt_final_bin_count :
    ∀ᶠ L : ℝ in atTop, ∀ P Q η : ℝ,
      1 ≤ P → P ≤ Q → 1 ≤ Real.log Q → 0 ≤ η → ∀ j : ℕ,
      Real.log (mrtBandUpper Q (j+1)) ≤ Real.sqrt L →
      ((mrtLogFamilyBins P Q η j).card:ℝ) ≤ Real.exp ((3/1000:ℝ)*L) := by
  filter_upwards [mrt_eventually_bin_count_budget,eventually_ge_atTop (1:ℝ)] with L hb hL
  intro P Q η hP hPQ hQ hη j hupper
  exact (mrt_final_bin_count_coarse hL hP hPQ hQ hη j hupper).trans hb

end TwoPointCorrelations

end OAI
