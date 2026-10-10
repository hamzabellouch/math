import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLiouvilleOscillatoryBounds
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningPositiveTransfer
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningResidualUniform

namespace OAI

/-! A fixed constant controls every oscillatory subinterval in the actual
escaping family. The fixed cutoff is chosen before the sequence index. -/

open Set Filter Topology
namespace DefocusingNLS

theorem spectralTurning_oscillatory_uniform
    (ell : ℕ → ℕ) (h : ℝ) (b omega gamma r₀ d E : ℕ → ℝ) (M : ℝ)
    (hh : h^2 = 1) (hM : 32 ≤ M) (hr₀ : Tendsto r₀ atTop atTop)
    (hdata : ∀ᶠ n in atTop, 0 < r₀ n ∧ 0 ≤ d n ∧ 0 ≤ b n ∧ b n ≤ 1 ∧
      |gamma n| ≤ 8 ∧ 2*r₀ n ≤ E n ∧
      (E n)^2 = 256*max ((ell n : ℝ)+1) (omega n) ∧
      homogeneousSpectralLocalizationFrequency h (b n)
        ((ell n : ℝ)*(ell n+10)) (omega n) (r₀ n) = 0 ∧
      spectralLiouvilleSlope ((ell n : ℝ)*(ell n+10)) (r₀ n)*(d n)^3 = 1) :
    ∀ᶠ n in atTop, ∀ q : ℝ → ℂ × ℂ, ContinuousOn q (Icc (r₀ n+M*d n) (E n)) →
      (∀ t ∈ Ioo (r₀ n+M*d n) (E n), HasDerivAt q (spectralScalarField
        ((homogeneousSpectralLocalizationFrequency h (b n) ((ell n : ℝ)*(ell n+10)) (omega n) t : ℂ)+
          Complex.I*(gamma n : ℂ)) (q t)) t) →
      ∀ r ∈ Icc (r₀ n+M*d n) (E n), ∀ t ∈ Icc (r₀ n+M*d n) (E n), r ≤ t →
        let k := fun s => Real.sqrt ‖spectralLiouvilleMomentum 1 h (b n)
          ((ell n : ℝ)*(ell n+10)) (omega n) (gamma n) s‖
        spectralShellNorm (k t) (q t) ≤ (25*Real.exp (2304+25/4))*spectralShellNorm (k r) (q r) ∧
        spectralShellNorm (k r) (q r) ≤ (25*Real.exp (2304+25/4))*spectralShellNorm (k t) (q t) := by
  let eta := fun n => (ell n : ℝ)*(ell n+10)
  have hsample : ∀ᶠ n in atTop, 0 < r₀ n ∧ 0 ≤ d n ∧ 0 ≤ eta n ∧
      spectralLiouvilleSlope (eta n) (r₀ n)*(d n)^3 = 1 := by
    filter_upwards [hdata] with n hn
    exact ⟨hn.1,hn.2.1,by dsimp only [eta]; positivity,hn.2.2.2.2.2.2.2.2⟩
  have hd := spectralTurningScale_tendsto eta r₀ d hr₀ hsample
  have he := spectralTurningOuterError_tendsto M r₀ d hr₀ hd
  have hsmallLimit : spectralTurningCutoffError M < 1 := by linarith [spectralTurningCutoffError_le M hM]
  filter_upwards [hdata,he.eventually (gt_mem_nhds hsmallLimit),
    hd.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    hr₀.eventually (eventually_ge_atTop (max 2 M))] with n hn hen hdn hrn
  have hr2 : 2 ≤ r₀ n := (le_max_left 2 M).trans hrn
  have hMr : M ≤ r₀ n := (le_max_right 2 M).trans hrn
  have hMp : 0 < M := by linarith
  have hdp : 0 < d n := by
    apply lt_of_le_of_ne hn.2.1
    intro heq
    have hs := hn.2.2.2.2.2.2.2.2
    rw [← heq] at hs
    norm_num at hs
  have hMd : M*d n ≤ r₀ n := by nlinarith
  let a := r₀ n+M*d n
  have ha : 0 < a := by dsimp only [a]; positivity
  have haE : a ≤ E n := by dsimp only [a]; linarith [hn.2.2.2.2.2.1]
  have hz : homogeneousSpectralLocalizationFrequency h (b n) (eta n) (omega n) (r₀ n) = 0 := hn.2.2.2.2.2.2.2.1
  have hsc : spectralLiouvilleSlope (eta n) (r₀ n)*(d n)^3 = 1 := hn.2.2.2.2.2.2.2.2
  have heta : 0 ≤ eta n := by dsimp only [eta]; positivity
  have hF (t : ℝ) (ht : t ∈ Icc a (E n)) : 0 < homogeneousSpectralLocalizationFrequency h (b n) (eta n) (omega n) t := by
    have hlt : r₀ n < t := by dsimp only [a] at ht; nlinarith [ht.1]
    have hm := homogeneousSpectralLocalizationFrequency_strictMono h (b n) (eta n) (omega n)
      heta hn.1 (ha.trans_le ht.1) hlt
    rwa [hz] at hm
  have hA : (∫ t in a..E n, 1/Real.sqrt
      (homogeneousSpectralLocalizationFrequency h (b n) (eta n) (omega n) t)) ≤ 288 := by
    simpa only [one_mul] using spectralTurning_positive_outer_phase (ell n) h (b n) (omega n)
      (r₀ n) (d n) M (E n) hh hn.2.2.1 hn.2.2.2.1 hn.1 hdp hMp hMd
      hn.2.2.2.2.2.1 hn.2.2.2.2.2.2.1 hz
  have hB : (∫ t in a..E n, ‖spectralLiouvilleResidual 1 h (b n) (eta n) (omega n) (gamma n) t‖/
      ‖spectralLiouvilleMomentum 1 h (b n) (eta n) (omega n) (gamma n) t‖) ≤ 1 :=
    (spectralTurning_outer_positive_error h (b n) (eta n) (omega n) (gamma n) (r₀ n) (d n)
      M (E n) heta hn.1 hdp hMp hMd hn.2.2.2.2.2.1 hz hsc).trans hen.le
  intro q hq hODE r hr t ht hrt
  have hb := spectralLiouville_oscillatory_subinterval h (b n) (eta n) (omega n) (gamma n)
    a (E n) 288 1 ha haE hF
    (fun s hs => spectralTurning_positive_derivative_small 1 h (b n) (eta n) (omega n) (gamma n)
      (r₀ n) (d n) M s (by norm_num) heta hr2 hdp hM hs.1 hz hsc)
    hA hB r t hr ht hrt q hq hODE
  have hNr : 0 ≤ spectralShellNorm (Real.sqrt ‖spectralLiouvilleMomentum 1 h (b n) (eta n)
      (omega n) (gamma n) r‖) (q r) := spectralShellNorm_nonneg _ (Real.sqrt_nonneg _) _
  have hNt : 0 ≤ spectralShellNorm (Real.sqrt ‖spectralLiouvilleMomentum 1 h (b n) (eta n)
      (omega n) (gamma n) t‖) (q t) := spectralShellNorm_nonneg _ (Real.sqrt_nonneg _) _
  have hexp : Real.exp (|gamma n| *288+(25/4)*1) ≤ Real.exp (2304+25/4) := by
    apply Real.exp_le_exp.mpr
    linarith [hn.2.2.2.2.1]
  have hc : 2*((25/4 : ℝ)*Real.exp (|gamma n| *288+(25/4)*1)) ≤ 25*Real.exp (2304+25/4) := by
    nlinarith [Real.exp_pos (2304+25/4)]
  have hc' : (25/4 : ℝ)*Real.exp (|gamma n| *288+(25/4)*1) ≤ 25*Real.exp (2304+25/4) := by
    nlinarith [Real.exp_pos (|gamma n| *288+(25/4)*1)]
  constructor
  · exact hb.1.trans (mul_le_mul_of_nonneg_right hc' hNr)
  · exact hb.2.trans (mul_le_mul_of_nonneg_right hc hNt)

end DefocusingNLS

end OAI
