import OAI.NumberTheory.TwoPoint.Halasz.HalaszOriginalShortMean
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTFinalBandBudget
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCommonDistance
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTShortMeanQuarterRate

namespace OAI

/-! The published short-mean rate with the exact original pretentious
cutoff and frequency range, for dyadic windows inside that cutoff. -/

namespace TwoPointCorrelations

open Filter Finset MeasureTheory
open scoped Classical

theorem halasz_first_original_short_mean
    (hprime : HalaszPrimeSparseInput) (hhigh : HalaszHighPrimeInput)
    (A : ℕ) (hA : 500000 ≤ A) :
    ∃ C H₀ : ℝ, 0 < C ∧ 1 ≤ H₀ ∧ ∀ᶠ N : ℕ in atTop,
      ∀ X : ℕ, N ≤ X → X ≤ N^3 →
      ∀ H : ℕ, H₀ ≤ H → (H:ℝ) ≤ Real.exp (Real.sqrt (Real.log N)) →
      ∀ F : ℕ → ℂ, F 1=1 → Multiplicative F → OneBounded F →
      ∀ M : ℝ, 0 ≤ M →
      (∀ u:ℝ, |u| ≤ X → M ≤ squaredDistance F (mrtArchimedeanTwist u) X) →
      (∫ x in (N:ℝ)..(2*N), ‖shortExponentialSum F H 0 x‖)/((N:ℝ)*H) ≤
        C*(Real.log (Real.log H)/Real.log H + Real.exp (-M/2)+(Real.log N)^(-1/700:ℝ)) := by
  obtain ⟨C₁,C₂,hC₁,hC₂,hmean⟩ := halasz_original_short_mean hprime hhigh
  obtain ⟨C₀,L₀,H₀,hC₀,hL₀,hH₀,hrate⟩ := mrt_short_mean_quarter_rate A hA C₁ C₂ hC₁.le hC₂.le
  obtain ⟨H₁,hscale⟩ := eventually_atTop.mp
    ((minor_arc_first_band_scale A 0 (by omega)).and (minor_arc_first_band_budget_eventually A hA))
  refine ⟨C₀,max H₀ H₁,hC₀,
    hH₀.trans (le_max_left _ _),?_⟩
  have hlog : Tendsto (fun N:ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hmean,mrt_common_final_band_from_budget,
    hlog.eventually (eventually_ge_atTop L₀),eventually_ge_atTop 2]
    with N hmean hband hLN hN2
  intro X hNX hXN H hH₀' hHN F hF1 hFm hFb M hM hd
  obtain ⟨hs,hbudget⟩ := hscale H ((le_max_right _ _).trans hH₀')
  obtain ⟨hH4,hLH,hLL,hP4,_,_,hPQ,hQU,_,hlQ⟩ := hs
  let P := minorArcFirstLower A H
  let Q := minorArcFirstUpper H
  have hL : 1 ≤ Real.log (N:ℝ) := hL₀.trans hLN
  have hHr : 0 < (H:ℝ) := by linarith
  have hH : 0 < H := by exact_mod_cast hHr
  have hN0 : 0 < (N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have hQ0 : 0 < Q := by dsimp [Q]; linarith
  have hQH : Q ≤ (H:ℝ) := hQU.trans
    (div_le_self hHr.le (one_le_pow₀ (by linarith : (1:ℝ)≤Real.log H)))
  have hlogH : Real.log (H:ℝ) ≤ Real.sqrt (Real.log N) := by
    have hh := Real.log_le_log hHr hHN
    simpa only [Real.log_exp] using hh
  have hlogQ : Real.log Q ≤ Real.sqrt (Real.log N) :=
    (Real.log_le_log hQ0 hQH).trans hlogH
  have hPN : 2 ≤ Real.log P := by
    dsimp [P]
    rw [minor_arc_first_lower_log]
    have hAr : (500000:ℝ) ≤ A := by exact_mod_cast hA
    nlinarith
  have hsqrt : Real.sqrt (Real.log N) ≤ Real.log N := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨by linarith,by nlinarith⟩
  have hHN' : H ≤ N := by
    have hh := hHN.trans (Real.exp_le_exp.mpr hsqrt)
    rw [Real.exp_log hN0] at hh
    exact_mod_cast hh
  have hsize : 2*Q ≤ (N:ℝ) := by
    have hp : (2:ℝ) ≤ Real.log (H:ℝ)^5 := hLH.trans
      (le_self_pow₀ (by linarith : (1:ℝ)≤Real.log H) (by norm_num : (5:ℕ)≠0))
    have hh := (le_div_iff₀ (pow_pos (by linarith : 0<Real.log (H:ℝ)) 5)).mp hQU
    have hn : (H:ℝ) ≤ N := by exact_mod_cast hHN'
    nlinarith
  have hres : 2 ≤ mrtBaseResolution P Q (1/100) := by
    have hh := mrt_first_resolution_lower A hA (by linarith) (by linarith)
      (by dsimp [Q] at hQ0 ⊢; linarith [hP4,hPQ]) hQH
    have hp : (2:ℝ) ≤ Real.log (H:ℝ)^100 := hLH.trans
      (le_self_pow₀ (by linarith : (1:ℝ)≤Real.log H) (by norm_num : (100:ℕ)≠0))
    exact hp.trans hh
  obtain ⟨J,hJ,_,hbands⟩ := hband P Q (by linarith) hlQ hlogQ hbudget
  have hm := hmean P Q (by dsimp [P]; linarith) hPQ hPN hlQ hbudget hres J hJ hbands
    X hNX hXN H (by exact_mod_cast (show (4:ℝ)≤H by linarith)) hHN' hsize F hF1 hFm hFb M hM hd
  exact hm.trans (hrate (Real.log N) hLN H ((le_max_left _ _).trans hH₀') M)

end TwoPointCorrelations

end OAI
