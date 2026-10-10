import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTExtraSmallIntegral
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTExtraEnergySum
import OAI.NumberTheory.TwoPoint.Halasz.HalaszLargePrimeEnergy

namespace OAI

/-! Complete additional-prime coarse-polynomial energy on the actual
no-small class. The prime sparse theorem and the pointwise cofactor saving
are explicit; all sample counts, set splits and bin sums are discharged. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

theorem mrt_no_small_coarse_energy (hprime : HalaszPrimeSparseInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ L : ℝ in Filter.atTop,
    ∀ (V : ℕ → Finset ℕ) (F : ℕ → ℂ), OneBounded F →
    ∀ J j : ℕ, j < J → ∀ P Q : ℝ, 1 ≤ P → P ≤ Q → 1 ≤ Real.log Q →
    2 ≤ mrtBaseResolution P Q (1/100) →
    (∀ p ∈ V (j+1), p.Prime) →
    (∀ p ∈ V (j+1), mrtBandLower P Q (j+1) ≤ (p:ℝ) ∧
      (p:ℝ) ≤ mrtBandUpper Q (j+1)) →
    200*Real.log L+1 ≤ Real.log (mrtBandLower P Q (j+1)) →
    Real.log (mrtBandUpper Q (j+1)) ≤ Real.sqrt L →
    ∀ N : ℕ, Real.exp L ≤ N → ∀ E : Set ℝ,
    MeasurableSet E → E ⊆ Set.Ioc (-Real.exp L) (Real.exp L) →
    (∀ t ∈ E, t ∈ mrtNoSmallBand (mrtLogFamilyBins P Q (1/100))
      (mrtLogFamilyPolynomial V F P Q (1/100))
      (mrtLogFamilyThreshold P Q (1/100)) J) →
    (∀ k ∈ mrtLogBins (mrtExtraPrimeResolution L) (mrtExtraPrimeLower L)
        (mrtExtraPrimeUpper L), ∀ t ∈ E,
      L^(-100:ℝ) ≤ ‖mrtLogPrimePolynomial
        (mrtPrimeBand (mrtExtraPrimeLower L) (mrtExtraPrimeUpper L)) F
          (mrtExtraPrimeResolution L) k t‖ →
      ‖mrtCofactorPolynomial (mrtPrimeBand (mrtExtraPrimeLower L) (mrtExtraPrimeUpper L))
        (mrtTypicalCoefficient (Icc 1 J) V F) N
        (mrtPrimeLogLower (mrtExtraPrimeResolution L) k) t‖ ≤ 2*L^(-1/40:ℝ)) →
    (∫ t in E, ‖mrtExtraCoarsePolynomial L (Icc 1 J) V F N t‖^2) ≤ C*L^(-1/80:ℝ) := by
  obtain ⟨C,B₀,hC,hB₀,hlarge⟩ := hprime.large_prime_product_energy
  refine ⟨4*1190408+4*(4*C),by positivity,?_⟩
  filter_upwards [hlarge,mrt_extra_small_integral,mrt_extra_band_geometry,
    (tendsto_rpow_atTop (show (0:ℝ)<1/80 by norm_num)).eventually
      (Filter.eventually_ge_atTop B₀),
    Filter.eventually_ge_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop (1:ℝ))]
    with L hlarge hsmall hg hHlarge hL hlog
  intro V F hF J j hj P Q hP hPQ hQ hres hp hrange hlo hhi N hN E hE hET hno hpoint
  let A := mrtPrimeBand (mrtExtraPrimeLower L) (mrtExtraPrimeUpper L)
  let H := mrtExtraPrimeResolution L
  let B := mrtTypicalCoefficient (Icc 1 J) V F
  let K := mrtLogBins H (mrtExtraPrimeLower L) (mrtExtraPrimeUpper L)
  have hL0 : 0 < L := by linarith
  have hH : 2 ≤ H := hg.1
  have hH0 : 0 < H := by linarith
  have hB : OneBounded B := mrtTypicalCoefficient_oneBounded _ _ _ hF
  have hT : 1 < Real.exp L := Real.one_lt_exp_iff.mpr hL0
  apply mrt_extra_coarse_energy hL hlog (Real.exp_pos L).le
    (by norm_num : (0:ℝ) ≤ 1190408) (show 0 ≤ 4*C by positivity) (Icc 1 J) V F N hET
    (fun k hk => (hg.2.2.2.2 k hk).2.1)
  intro k hk
  let Y := mrtPrimeLogLower H k
  let Qk := mrtLogPrimePolynomial A F H k
  let Rk := mrtCofactorPolynomial A B N Y
  let D := {t | L^(-100:ℝ) ≤ ‖Qk t‖}
  have hQc : Continuous Qk := mrt_log_prime_polynomial_continuous _ _ _ _
  have hRc : Continuous Rk := mrtCofactorPolynomial_continuous _ _ _ _
  have hD : MeasurableSet D := (isClosed_le continuous_const hQc.norm).measurableSet
  have hS : (∫ t in E \ D, ‖Qk t*Rk t‖^2) ≤ 1190408*(L^(-100:ℝ))^2 := by
    apply hsmall V F hF J j hj P Q hP hPQ hQ hres hp hrange hlo hhi
      (Real.exp L) hT le_rfl N hN B hB k hk (E \ D) (hE.diff hD)
      (fun t ht => hET ht.1) (fun t ht => hno t ht.1)
    intro t ht
    exact (lt_of_not_ge ht.2).le
  have hY := hg.2.2.2.2 k hk
  have hY0 : 0 < Y := by change 0 < mrtPrimeLogLower H k; exact lt_trans zero_lt_one hY.1
  have hlogY : 1 ≤ Real.log Y :=
    (Real.one_le_rpow hL (by norm_num : (0:ℝ) ≤ 79/80)).trans hY.2.1
  have hY2 : 2 ≤ Y := by linarith [Real.log_le_sub_one_of_pos hY0]
  have hHY : H^2 ≤ Y := by
    have he : H^2=L^(1/40:ℝ) := by
      change (L^(1/80:ℝ))^2=L^(1/40:ℝ)
      rw [← Real.rpow_natCast,← Real.rpow_mul hL0.le]
      norm_num
    rw [he]
    calc
      _ ≤ L^(79/80:ℝ) := Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
      _ ≤ Real.log Y := hY.2.1
      _ ≤ Y := by linarith [Real.log_le_sub_one_of_pos hY0]
  have hdata (p : ℕ) (hp' : p ∈ A.filter (fun p => mrtPrimeLogBin H p=k)) :
      p.Prime ∧ Y ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*Y := by
    have hpp := mrtPrimeBand_prime (mem_filter.mp hp').1
    have hh := mrt_prime_log_bin_bounds hH0 hpp.one_lt.le
    rw [(mem_filter.mp hp').2] at hh
    refine ⟨hpp,hh.1,hh.2.trans ?_⟩
    exact mul_le_mul_of_nonneg_right (mrt_prime_log_width hH).2.1 hY0.le
  have hwindow (p : ℕ) (hp' : p ∈ A.filter (fun p => mrtPrimeLogBin H p=k)) :
      Real.log Y ≤ Real.log (p:ℝ) ∧ Real.log (p:ℝ) ≤ Real.log Y+1/H := by
    have hpp := (hdata p hp').1
    have hh := mrt_prime_log_bin_bounds hH0 hpp.one_lt.le
    rw [(mem_filter.mp hp').2] at hh
    refine ⟨Real.log_le_log hY0 hh.1,?_⟩
    have hu := Real.log_le_log (by exact_mod_cast hpp.pos) hh.2
    change Real.log (p:ℝ) ≤ Real.log (Real.exp (1/H)*Y) at hu
    simpa only [Real.log_mul (Real.exp_ne_zero _) hY0.ne',Real.log_exp,add_comm] using hu
  have hG := hlarge H Y hHlarge hY2 hHY hY.2.1 hY.2.2 hlogY
    (A.filter (fun p => mrtPrimeLogBin H p=k)) F hdata hwindow hF
    A B N Y (2*L^(-1/40:ℝ)) (by positivity) E hE hET (hpoint k hk)
  have hh := mrt_product_energy_split Qk Rk hQc hRc (Real.exp_pos L).le hET hS hG
  convert hh using 1
  ring

end TwoPointCorrelations

end OAI
