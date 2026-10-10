import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTFinalSampleScale

namespace OAI

/-! The optimized moment applied to every actual logarithmic bin in the
last-band witness cover. No abstract covering family is assumed. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

theorem mrt_no_small_final_samples :
    ∀ᶠ L : ℝ in Filter.atTop,
    ∀ (V : ℕ → Finset ℕ) (F : ℕ → ℂ), OneBounded F →
    ∀ J j : ℕ, j < J → ∀ P Q : ℝ, 1 ≤ Real.log Q →
    2 ≤ mrtBaseResolution P Q (1/100) →
    (∀ p ∈ V (j+1), p.Prime) →
    (∀ p ∈ V (j+1), mrtBandLower P Q (j+1) ≤ (p:ℝ) ∧
      (p:ℝ) ≤ mrtBandUpper Q (j+1)) →
    200*Real.log L+1 ≤ Real.log (mrtBandLower P Q (j+1)) →
    Real.log (mrtBandUpper Q (j+1)) ≤ Real.sqrt L →
    ∀ T : ℝ, 1 < T → T ≤ Real.exp L → ∀ S : Finset ℝ,
    (∀ t ∈ S, |t| ≤ T) →
    (∀ t ∈ S, ∀ s ∈ S, t≠s → 1 ≤ |t-s|) →
    (∀ t ∈ S, t ∈ mrtNoSmallBand (mrtLogFamilyBins P Q (1/100))
      (mrtLogFamilyPolynomial V F P Q (1/100))
      (mrtLogFamilyThreshold P Q (1/100)) J) →
    (S.card:ℝ) ≤ (mrtLogFamilyBins P Q (1/100) j).card *
      Real.exp ((99/200:ℝ)*L) := by
  filter_upwards [mrt_final_prime_large_samples,
    Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop (1:ℝ))]
    with L hfinal hLL
  intro V F hF J j hj P Q hQ hres hprime hrange hlo hhi T hT hTU S hS hsep hno
  let H := mrtResolution P Q (1/100) (j+1)
  let K := mrtLogFamilyBins P Q (1/100) j
  let S' := fun k => S.filter (fun t => mrtLogFamilyThreshold P Q (1/100) j k <
    ‖mrtLogFamilyPolynomial V F P Q (1/100) j k t‖)
  have hH : 2 ≤ H := by
    have hj1 : (1:ℝ) ≤ (j+1:ℕ) := by exact_mod_cast (show 1 ≤ j+1 by omega)
    have hs : 1 ≤ ((j+1:ℕ):ℝ)^2 := one_le_pow₀ hj1
    dsimp [H,mrtResolution]
    nlinarith [mrtBaseResolution_pos P Q (1/100)]
  have hH0 : 0 < H := by linarith
  have hBU : 1 ≤ mrtBandUpper Q (j+1) := by
    have hlogQ : 0 ≤ Real.log Q := by linarith
    unfold mrtBandUpper
    exact Real.one_le_exp (by positivity)
  have hd := mrt_log_bin_prime_data (V (j+1)) hH (Real.exp_pos _) hprime hrange
  have hcover : S ⊆ K.biUnion S' := by
    intro t ht
    obtain ⟨k,hk,htk⟩ := mrt_no_small_band_large_witness
      (mrtLogFamilyBins P Q (1/100)) (mrtLogFamilyPolynomial V F P Q (1/100))
      (mrtLogFamilyThreshold P Q (1/100)) hj (hno t ht)
    exact mem_biUnion.mpr ⟨k,hk,mem_filter.mpr ⟨ht,htk⟩⟩
  have hcard : (S.card:ℝ) ≤ ∑ k ∈ K, ((S' k).card:ℝ) := by
    exact_mod_cast (card_le_card hcover).trans card_biUnion_le
  apply hcard.trans
  calc
    _ ≤ ∑ _k ∈ K, Real.exp ((99/200:ℝ)*L) := by
      apply sum_le_sum
      intro k hk
      let Y := mrtPrimeLogLower H k
      have hYlow : 200*Real.log L ≤ Real.log Y := by
        have hh := mrt_log_bin_lower_endpoint (by linarith : 1 ≤ H)
          (Real.exp_pos _) (mem_Icc.mp hk).1
        have hh' := Real.log_le_log (mul_pos (Real.exp_pos _) (Real.exp_pos _)) hh
        rw [Real.log_mul (Real.exp_ne_zero _) (Real.exp_ne_zero _),Real.log_exp] at hh'
        change -1+Real.log (mrtBandLower P Q (j+1)) ≤ Real.log Y at hh'
        linarith
      have hY : 1 < Y := (Real.one_lt_exp_iff.mpr
        (show 0 < (k:ℝ)/H by
          have hh : 0 < Real.log Y := by linarith
          simpa only [Y,mrtPrimeLogLower,Real.log_exp] using hh))
      have hYhi : Real.log Y ≤ Real.sqrt L :=
        (Real.log_le_log (by linarith : 0 < Y)
          (mrt_prime_log_lower_le_upper hH0 hBU (mem_Icc.mp hk).2)).trans hhi
      let α := mrtFrequencyExponent (1/100) j
      have hα : 0 ≤ α := mrtFrequencyExponent_nonneg (by norm_num) (by norm_num) j
      have hαu : α ≤ 6/25 := by
        have hh := (mrtFrequencyExponent_bounds (show (0:ℝ) ≤ 1/100 by norm_num) j).2
        exact hh.trans_eq (by norm_num)
      apply hfinal Y T α hY hYlow hYhi hT hTU hα hαu
        ((V (j+1)).filter (fun p => mrtPrimeLogBin H p = k))
        (fun p hp => hprime p (mem_filter.mp hp).1)
        (fun p hp => ?_) F hF (S' k)
        (fun t ht => hS t (mem_filter.mp ht).1)
        (fun t ht s hs hts => hsep t (mem_filter.mp ht).1 s (mem_filter.mp hs).1 hts)
        (fun t ht => ?_)
      · have hh := hd.2 p (mem_filter.mp hp).1
        have hu := hh.2.trans (mul_le_mul_of_nonneg_right
          (mrt_prime_log_width hH).2.1 (Real.exp_pos _).le)
        simpa only [(mem_filter.mp hp).2] using And.intro hh.1 hu
      · exact (mem_filter.mp ht).2.le
    _ = _ := by simp [K]

end TwoPointCorrelations

end OAI
