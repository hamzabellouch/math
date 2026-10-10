import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningOutgoingConnection
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningConeError
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLiouvilleReflectedCone
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralScalarNonzero
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningOuterDerivative

namespace OAI

/-! The actual outgoing comparison enters the fixed inner Robin cone along
an escaping subsequence. Its turning coefficients and small-error hypotheses
are all supplied by the preceding construction. -/

open Set Filter Topology
namespace DefocusingNLS

theorem spectralTurning_outgoing_inner_cone
    (ell : ℕ → ℕ) (h : ℝ) (b omega gamma r₀ d E : ℕ → ℝ) (R : ℝ)
    (hh : h^2 = 1) (hR : 0 < R) (hr₀ : Tendsto r₀ atTop atTop)
    (hdata : ∀ᶠ n in atTop, 0 < r₀ n ∧ 0 ≤ d n ∧ 0 ≤ b n ∧ b n ≤ 1 ∧
      |gamma n| ≤ 8 ∧ 2*r₀ n ≤ E n ∧
      (E n)^2 = 256*max ((ell n : ℝ)+1) (omega n) ∧
      homogeneousSpectralLocalizationFrequency h (b n)
        ((ell n : ℝ)*(ell n+10)) (omega n) (r₀ n) = 0 ∧
      spectralLiouvilleSlope ((ell n : ℝ)*(ell n+10)) (r₀ n)*(d n)^3 = 1) :
    ∃ (q : ℕ → ℝ → ℂ × ℂ) (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ᶠ n in atTop, Continuous (q n) ∧
        q n (E n) = spectralOscillatoryData h (Real.sqrt (Real.sqrt
          (homogeneousSpectralLocalizationFrequency h (b n)
            ((ell n : ℝ)*(ell n+10)) (omega n) (E n)))) ∧
        spectralScalarFlux (q n (E n)) = h ∧
        ∀ t ∈ Icc R (E n), HasDerivAt (q n) (spectralScalarField
          ((homogeneousSpectralLocalizationFrequency h (b n)
            ((ell n : ℝ)*(ell n+10)) (omega n) t : ℂ)+Complex.I*(gamma n : ℂ))
          (q n t)) t) ∧
      ∀ᶠ n in atTop,
        let p := spectralLiouvilleMomentum (-1) h (b (φ n)) ((ell (φ n) : ℝ)*(ell (φ n)+10))
          (omega (φ n)) (gamma (φ n)) R
        (q (φ n) R).1 ≠ 0 ∧
          ‖(q (φ n) R).2+(p-(spectralLiouvilleSlope ((ell (φ n) : ℝ)*(ell (φ n)+10)) R : ℂ)/
            (4*p^2))*(q (φ n) R).1‖ ≤ (1/2 : ℝ)*‖p‖*‖(q (φ n) R).1‖ := by
  obtain ⟨q,φ,hφ,hq,hmargin⟩ := spectralTurning_outgoing_growing_connection
    ell h b omega gamma r₀ d E R hh hR hr₀ hdata
  let eta := fun n => (ell (φ n) : ℝ)*(ell (φ n)+10)
  have hsample : ∀ᶠ n in atTop, 0 < r₀ (φ n) ∧ 0 ≤ d (φ n) ∧ 0 ≤ eta n ∧
      homogeneousSpectralLocalizationFrequency h (b (φ n)) (eta n) (omega (φ n)) (r₀ (φ n)) = 0 ∧
      spectralLiouvilleSlope (eta n) (r₀ (φ n))*(d (φ n))^3 = 1 := by
    filter_upwards [hφ.tendsto_atTop.eventually hdata] with n hn
    exact ⟨hn.1,hn.2.1,by dsimp only [eta]; positivity,
      hn.2.2.2.2.2.2.2.1,hn.2.2.2.2.2.2.2.2⟩
  have hrt := hr₀.comp hφ.tendsto_atTop
  have hd := spectralTurningScale_tendsto eta (fun n => r₀ (φ n)) (fun n => d (φ n)) hrt
    (hsample.mono (fun n hn => ⟨hn.1,hn.2.1,hn.2.2.1,hn.2.2.2.2⟩))
  have herr := spectralTurning_eventual_cone_error h (fun n => b (φ n)) eta
    (fun n => omega (φ n)) (fun n => gamma (φ n)) (fun n => r₀ (φ n))
    (fun n => d (φ n)) R hR hrt hsample
  obtain ⟨M,hMm,hMe⟩ := (hmargin.and herr).exists
  have hM : 32 ≤ M := hMe.1
  have hMp : 0 < M := by linarith
  refine ⟨q,φ,hφ,hq,?_⟩
  filter_upwards [hφ.tendsto_atTop.eventually hq,hφ.tendsto_atTop.eventually hdata,
    hsample,hMm,hMe.2,hd.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    hrt.eventually (eventually_ge_atTop (max (16/R) (max (2*R) (2*M))))]
    with n hqn hdn hsn hmn hen hsmalln hlarge
  dsimp only [Function.comp_def] at hlarge
  let c := r₀ (φ n)-M*d (φ n)
  have hdp : 0 < d (φ n) := by
    apply lt_of_le_of_ne hsn.2.1
    intro he
    have hs := hsn.2.2.2.2
    rw [← he] at hs
    norm_num at hs
  have hRM := (le_max_right (16/R) (max (2*R) (2*M))).trans hlarge
  have hRhalf : R ≤ r₀ (φ n)/2 := by linarith [le_trans (le_max_left (2*R) (2*M)) hRM]
  have hMd : M*d (φ n) ≤ r₀ (φ n)/2 := by nlinarith [le_trans (le_max_right (2*R) (2*M)) hRM]
  have hprod : 16 ≤ r₀ (φ n)*R := by
    have hl := mul_le_mul_of_nonneg_right ((le_max_left (16/R) (max (2*R) (2*M))).trans hlarge) hR.le
    have he : (16/R)*R = 16 := by field_simp
    rwa [he] at hl
  have hRc : R ≤ c := by dsimp only [c]; linarith
  have hct : c < r₀ (φ n) := by dsimp only [c]; nlinarith
  have hcE : c ≤ E (φ n) := hct.le.trans (by linarith [hdn.2.2.2.2.2.1])
  have hF (t : ℝ) (ht : t ∈ Icc R c) :
      0 < (-1)*homogeneousSpectralLocalizationFrequency h (b (φ n)) (eta n) (omega (φ n)) t := by
    have hf := homogeneousSpectralLocalizationFrequency_strictMono h (b (φ n)) (eta n) (omega (φ n))
      hsn.2.2.1 (hR.trans_le ht.1) hsn.1 (ht.2.trans_lt hct)
    rw [hsn.2.2.2.1] at hf
    linarith
  have hVp : ContinuousOn (fun t =>
      (homogeneousSpectralLocalizationFrequency h (b (φ n)) (eta n) (omega (φ n)) t : ℂ)+
        Complex.I*(gamma (φ n) : ℂ)) (Icc c (E (φ n))) :=
    (Complex.continuous_ofReal.comp_continuousOn (fun t ht =>
      (homogeneousSpectralLocalizationFrequency_hasDerivAt h (b (φ n)) (eta n) (omega (φ n)) t
        (hR.trans_le (hRc.trans ht.1))).continuousAt.continuousWithinAt)).add continuousOn_const
  have hqE : q (φ n) (E (φ n)) ≠ 0 := by
    intro he
    have hf := hqn.2.2.1
    rw [he] at hf
    have hz : spectralScalarFlux (0 : ℂ × ℂ) = 0 := by simp [spectralScalarFlux]
    rw [hz] at hf
    nlinarith [hh]
  have hqc : q (φ n) c ≠ 0 := spectralScalar_ne_zero_of_right c (E (φ n)) hcE _ hVp _
    hqn.1.continuousOn (fun t ht => hqn.2.2.2 t ⟨hRc.trans ht.1.le,ht.2.le⟩) hqE
  have hk : 0 < Real.sqrt ‖spectralLiouvilleMomentum (-1) h (b (φ n)) (eta n)
      (omega (φ n)) (gamma (φ n)) c‖ :=
    spectralLiouville_norm_weight_pos (-1) h (b (φ n)) (eta n) (omega (φ n)) (gamma (φ n)) c
      (by norm_num) (by intro he; have hf := hF c ⟨hRc,le_rfl⟩; rw [he,mul_zero] at hf; linarith)
  have hN : 0 < spectralShellNorm (Real.sqrt ‖spectralLiouvilleMomentum (-1) h (b (φ n))
      (eta n) (omega (φ n)) (gamma (φ n)) c‖) (q (φ n) c) := by
    by_contra hbad
    have hz := le_antisymm (le_of_not_gt hbad) (spectralShellNorm_nonneg _ hk.le _)
    exact hqc ((spectralShellNorm_eq_zero _ hk _).mp hz)
  apply spectralLiouville_reflected_cone h (b (φ n)) (eta n) (omega (φ n)) (gamma (φ n)) R c
    hR hRc hF
    (fun t ht => spectralTurning_negative_derivative_small (-1) h (b (φ n)) (eta n)
      (omega (φ n)) (gamma (φ n)) (r₀ (φ n)) (d (φ n)) M R t (by norm_num)
      hsn.2.2.1 hsn.1 hdp hM hR hprod ht.1 ht.2 hsn.2.2.2.1 hsn.2.2.2.2)
    (q (φ n)) hqn.1.continuousOn
    (fun t ht => hqn.2.2.2 t ⟨ht.1.le,ht.2.le.trans hcE⟩) hN
  · simpa only [eta, c, div_eq_mul_inv, mul_comm, one_mul] using hmn
  · exact hen

theorem spectralTurning_outgoing_relative_bounds
    (ell : ℕ → ℕ) (h : ℝ) (b omega gamma r₀ d E : ℕ → ℝ) (R : ℝ)
    (hh : h^2 = 1) (hR : 0 < R) (hr₀ : Tendsto r₀ atTop atTop)
    (hdata : ∀ᶠ n in atTop, 0 < r₀ n ∧ 0 ≤ d n ∧ 0 ≤ b n ∧ b n ≤ 1 ∧
      |gamma n| ≤ 8 ∧ 2*r₀ n ≤ E n ∧
      (E n)^2 = 256*max ((ell n : ℝ)+1) (omega n) ∧
      homogeneousSpectralLocalizationFrequency h (b n)
        ((ell n : ℝ)*(ell n+10)) (omega n) (r₀ n) = 0 ∧
      spectralLiouvilleSlope ((ell n : ℝ)*(ell n+10)) (r₀ n)*(d n)^3 = 1) :
    ∃ (q : ℕ → ℝ → ℂ × ℂ) (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ᶠ n in atTop, Continuous (q n) ∧
        q n (E n) = spectralOscillatoryData h (Real.sqrt (Real.sqrt
          (homogeneousSpectralLocalizationFrequency h (b n)
            ((ell n : ℝ)*(ell n+10)) (omega n) (E n)))) ∧
        spectralScalarFlux (q n (E n)) = h ∧
        ∀ t ∈ Icc R (E n), HasDerivAt (q n) (spectralScalarField
          ((homogeneousSpectralLocalizationFrequency h (b n)
            ((ell n : ℝ)*(ell n+10)) (omega n) t : ℂ)+Complex.I*(gamma n : ℂ))
          (q n t)) t) ∧
      ∀ eps : ℝ, 0 < eps → ∃ M : ℝ, 32 ≤ M ∧ ∀ᶠ n in atTop,
        let p := spectralLiouvilleMomentum (-1) h (b (φ n)) ((ell (φ n) : ℝ)*(ell (φ n)+10))
          (omega (φ n)) (gamma (φ n)) R
        ((q (φ n) R).1 ≠ 0 ∧
          ‖(q (φ n) R).2+(p-(spectralLiouvilleSlope ((ell (φ n) : ℝ)*(ell (φ n)+10)) R : ℂ)/
            (4*p^2))*(q (φ n) R).1‖ ≤ eps*‖p‖*‖(q (φ n) R).1‖) ∧
        (1/16 : ℝ)*Real.exp ((∫ t in R..(r₀ (φ n)-M*d (φ n)),
          spectralLiouvilleMomentum (-1) h (b (φ n)) ((ell (φ n) : ℝ)*(ell (φ n)+10))
            (omega (φ n)) (gamma (φ n)) t).re)*
          spectralShellNorm (Real.sqrt ‖spectralLiouvilleMomentum (-1) h (b (φ n))
            ((ell (φ n) : ℝ)*(ell (φ n)+10)) (omega (φ n)) (gamma (φ n))
            (r₀ (φ n)-M*d (φ n))‖) (q (φ n) (r₀ (φ n)-M*d (φ n))) ≤
          Real.sqrt ‖p‖*‖(q (φ n) R).1‖ := by
  obtain ⟨q,φ,hφ,hq,hmargin⟩ := spectralTurning_outgoing_growing_connection
    ell h b omega gamma r₀ d E R hh hR hr₀ hdata
  refine ⟨q,φ,hφ,hq,?_⟩
  intro eps heps
  let eta := fun n => (ell (φ n) : ℝ)*(ell (φ n)+10)
  have hsample : ∀ᶠ n in atTop, 0 < r₀ (φ n) ∧ 0 ≤ d (φ n) ∧ 0 ≤ eta n ∧
      homogeneousSpectralLocalizationFrequency h (b (φ n)) (eta n) (omega (φ n)) (r₀ (φ n)) = 0 ∧
      spectralLiouvilleSlope (eta n) (r₀ (φ n))*(d (φ n))^3 = 1 := by
    filter_upwards [hφ.tendsto_atTop.eventually hdata] with n hn
    exact ⟨hn.1,hn.2.1,by dsimp only [eta]; positivity,
      hn.2.2.2.2.2.2.2.1,hn.2.2.2.2.2.2.2.2⟩
  have hrt := hr₀.comp hφ.tendsto_atTop
  have hd := spectralTurningScale_tendsto eta (fun n => r₀ (φ n)) (fun n => d (φ n)) hrt
    (hsample.mono (fun n hn => ⟨hn.1,hn.2.1,hn.2.2.1,hn.2.2.2.2⟩))
  have herr := spectralTurning_eventual_relative_error (min (1/16) (eps/40))
    (lt_min (by norm_num) (by positivity)) h (fun n => b (φ n)) eta
    (fun n => omega (φ n)) (fun n => gamma (φ n)) (fun n => r₀ (φ n))
    (fun n => d (φ n)) R hR hrt hsample
  obtain ⟨M,hMm,hMe⟩ := (hmargin.and herr).exists
  have hM : 32 ≤ M := hMe.1
  have hMp : 0 < M := by linarith
  refine ⟨M,hM,?_⟩
  filter_upwards [hφ.tendsto_atTop.eventually hq,hφ.tendsto_atTop.eventually hdata,
    hsample,hMm,hMe.2,hd.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    hrt.eventually (eventually_ge_atTop (max (16/R) (max (2*R) (2*M))))]
    with n hqn hdn hsn hmn hen hsmalln hlarge
  dsimp only [Function.comp_def] at hlarge
  let c := r₀ (φ n)-M*d (φ n)
  have hdp : 0 < d (φ n) := by
    apply lt_of_le_of_ne hsn.2.1
    intro he
    have hs := hsn.2.2.2.2
    rw [← he] at hs
    norm_num at hs
  have hRM := (le_max_right (16/R) (max (2*R) (2*M))).trans hlarge
  have hRhalf : R ≤ r₀ (φ n)/2 := by linarith [le_trans (le_max_left (2*R) (2*M)) hRM]
  have hMd : M*d (φ n) ≤ r₀ (φ n)/2 := by nlinarith [le_trans (le_max_right (2*R) (2*M)) hRM]
  have hprod : 16 ≤ r₀ (φ n)*R := by
    have hl := mul_le_mul_of_nonneg_right ((le_max_left (16/R) (max (2*R) (2*M))).trans hlarge) hR.le
    have he : (16/R)*R = 16 := by field_simp
    rwa [he] at hl
  have hRc : R ≤ c := by dsimp only [c]; linarith
  have hct : c < r₀ (φ n) := by dsimp only [c]; nlinarith
  have hcE : c ≤ E (φ n) := hct.le.trans (by linarith [hdn.2.2.2.2.2.1])
  have hF (t : ℝ) (ht : t ∈ Icc R c) :
      0 < (-1)*homogeneousSpectralLocalizationFrequency h (b (φ n)) (eta n) (omega (φ n)) t := by
    have hf := homogeneousSpectralLocalizationFrequency_strictMono h (b (φ n)) (eta n) (omega (φ n))
      hsn.2.2.1 (hR.trans_le ht.1) hsn.1 (ht.2.trans_lt hct)
    rw [hsn.2.2.2.1] at hf
    linarith
  have hVp : ContinuousOn (fun t =>
      (homogeneousSpectralLocalizationFrequency h (b (φ n)) (eta n) (omega (φ n)) t : ℂ)+
        Complex.I*(gamma (φ n) : ℂ)) (Icc c (E (φ n))) :=
    (Complex.continuous_ofReal.comp_continuousOn (fun t ht =>
      (homogeneousSpectralLocalizationFrequency_hasDerivAt h (b (φ n)) (eta n) (omega (φ n)) t
        (hR.trans_le (hRc.trans ht.1))).continuousAt.continuousWithinAt)).add continuousOn_const
  have hqE : q (φ n) (E (φ n)) ≠ 0 := by
    intro he
    have hf := hqn.2.2.1
    rw [he] at hf
    have hz : spectralScalarFlux (0 : ℂ × ℂ) = 0 := by simp [spectralScalarFlux]
    rw [hz] at hf
    nlinarith [hh]
  have hqc : q (φ n) c ≠ 0 := spectralScalar_ne_zero_of_right c (E (φ n)) hcE _ hVp _
    hqn.1.continuousOn (fun t ht => hqn.2.2.2 t ⟨hRc.trans ht.1.le,ht.2.le⟩) hqE
  have hk : 0 < Real.sqrt ‖spectralLiouvilleMomentum (-1) h (b (φ n)) (eta n)
      (omega (φ n)) (gamma (φ n)) c‖ :=
    spectralLiouville_norm_weight_pos (-1) h (b (φ n)) (eta n) (omega (φ n)) (gamma (φ n)) c
      (by norm_num) (by intro he; have hf := hF c ⟨hRc,le_rfl⟩; rw [he,mul_zero] at hf; linarith)
  have hN : 0 < spectralShellNorm (Real.sqrt ‖spectralLiouvilleMomentum (-1) h (b (φ n))
      (eta n) (omega (φ n)) (gamma (φ n)) c‖) (q (φ n) c) := by
    by_contra hbad
    have hz := le_antisymm (le_of_not_gt hbad) (spectralShellNorm_nonneg _ hk.le _)
    exact hqc ((spectralShellNorm_eq_zero _ hk _).mp hz)
  apply spectralLiouville_reflected_relative_bounds eps heps h (b (φ n)) (eta n) (omega (φ n)) (gamma (φ n)) R c
    hR hRc hF
    (fun t ht => spectralTurning_negative_derivative_small (-1) h (b (φ n)) (eta n)
      (omega (φ n)) (gamma (φ n)) (r₀ (φ n)) (d (φ n)) M R t (by norm_num)
      hsn.2.2.1 hsn.1 hdp hM hR hprod ht.1 ht.2 hsn.2.2.2.1 hsn.2.2.2.2)
    (q (φ n)) hqn.1.continuousOn
    (fun t ht => hqn.2.2.2 t ⟨ht.1.le,ht.2.le.trans hcE⟩) hN
  · simpa only [eta, c, div_eq_mul_inv, mul_comm, one_mul] using hmn
  · exact hen

theorem spectralTurning_outgoing_relative_cone
    (ell : ℕ → ℕ) (h : ℝ) (b omega gamma r₀ d E : ℕ → ℝ) (R : ℝ)
    (hh : h^2 = 1) (hR : 0 < R) (hr₀ : Tendsto r₀ atTop atTop)
    (hdata : ∀ᶠ n in atTop, 0 < r₀ n ∧ 0 ≤ d n ∧ 0 ≤ b n ∧ b n ≤ 1 ∧
      |gamma n| ≤ 8 ∧ 2*r₀ n ≤ E n ∧
      (E n)^2 = 256*max ((ell n : ℝ)+1) (omega n) ∧
      homogeneousSpectralLocalizationFrequency h (b n)
        ((ell n : ℝ)*(ell n+10)) (omega n) (r₀ n) = 0 ∧
      spectralLiouvilleSlope ((ell n : ℝ)*(ell n+10)) (r₀ n)*(d n)^3 = 1) :
    ∃ (q : ℕ → ℝ → ℂ × ℂ) (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ᶠ n in atTop, Continuous (q n) ∧
        q n (E n) = spectralOscillatoryData h (Real.sqrt (Real.sqrt
          (homogeneousSpectralLocalizationFrequency h (b n)
            ((ell n : ℝ)*(ell n+10)) (omega n) (E n)))) ∧
        spectralScalarFlux (q n (E n)) = h ∧
        ∀ t ∈ Icc R (E n), HasDerivAt (q n) (spectralScalarField
          ((homogeneousSpectralLocalizationFrequency h (b n)
            ((ell n : ℝ)*(ell n+10)) (omega n) t : ℂ)+Complex.I*(gamma n : ℂ))
          (q n t)) t) ∧
      ∀ eps : ℝ, 0 < eps → ∀ᶠ n in atTop,
        let p := spectralLiouvilleMomentum (-1) h (b (φ n)) ((ell (φ n) : ℝ)*(ell (φ n)+10))
          (omega (φ n)) (gamma (φ n)) R
        (q (φ n) R).1 ≠ 0 ∧
          ‖(q (φ n) R).2+(p-(spectralLiouvilleSlope ((ell (φ n) : ℝ)*(ell (φ n)+10)) R : ℂ)/
            (4*p^2))*(q (φ n) R).1‖ ≤ eps*‖p‖*‖(q (φ n) R).1‖ := by
  obtain ⟨q,φ,hφ,hq,hbounds⟩ := spectralTurning_outgoing_relative_bounds
    ell h b omega gamma r₀ d E R hh hR hr₀ hdata
  refine ⟨q,φ,hφ,hq,?_⟩
  intro eps heps
  obtain ⟨M,_,hM⟩ := hbounds eps heps
  exact hM.mono (fun _ hn => hn.1)

end DefocusingNLS

end OAI
