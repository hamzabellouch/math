import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningGreen
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningInnerCone
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningOuterWeight
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningOscillatoryUniform

namespace OAI

/-! The actual normalized outgoing family has a uniformly bounded Green
kernel on the full interval from the fixed inner radius to the remote radius. -/

open Set Filter Topology MeasureTheory
namespace DefocusingNLS

theorem spectralTurning_outgoing_green_extension_uniform
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
      ∃ K J : ℝ, 0 ≤ K ∧ 0 ≤ J ∧ ∀ᶠ n in atTop,
        let k := spectralTurningRegularizedWeight h (b (φ n))
          ((ell (φ n) : ℝ)*(ell (φ n)+10)) (omega (φ n)) (gamma (φ n)) (d (φ n))
        ∃ (Y : ℝ → ℂ × ℂ) (W : ℂ), Continuous Y ∧ Y R = (0,(k R : ℂ)) ∧
          (∀ t ∈ Icc R (E (φ n)), HasDerivAt Y (spectralScalarField
            ((homogeneousSpectralLocalizationFrequency h (b (φ n))
              ((ell (φ n) : ℝ)*(ell (φ n)+10)) (omega (φ n)) t : ℂ)+
                Complex.I*(gamma (φ n) : ℂ)) (Y t)) t) ∧
          W ≠ 0 ∧ (∀ t ∈ Icc R (E (φ n)), spectralScalarWronskian (Y t) (q (φ n) t) = W) ∧
          (∀ r ∈ Icc R (E (φ n)), ∀ t ∈ Icc R (E (φ n)),
            spectralShellNorm (k r) (spectralScalarGreenState Y (q (φ n)) W r t) ≤ K/(k t)) ∧
          ∀ z : ℂ, ∀ r ∈ Icc R (E (φ n)),
            spectralShellNorm (k r) ((z/(q (φ n) R).1) • q (φ n) r) ≤ J*k R*‖z‖ := by
  obtain ⟨q,φ,hφ,hq,hbounds⟩ := spectralTurning_outgoing_relative_bounds
    ell h b omega gamma r₀ d E R hh hR hr₀ hdata
  obtain ⟨M,hM,hvalue⟩ := hbounds 1 (by norm_num)
  let eta := fun n => (ell (φ n) : ℝ)*(ell (φ n)+10)
  let bs := fun n => b (φ n)
  let os := fun n => omega (φ n)
  let gs := fun n => gamma (φ n)
  let rs := fun n => r₀ (φ n)
  let ds := fun n => d (φ n)
  let es := fun n => E (φ n)
  have hrt : Tendsto rs atTop atTop := hr₀.comp hφ.tendsto_atTop
  have hs : ∀ᶠ n in atTop, 0 < rs n ∧ 0 ≤ ds n ∧ 0 ≤ eta n ∧ |gs n| ≤ 8 ∧
      homogeneousSpectralLocalizationFrequency h (bs n) (eta n) (os n) (rs n) = 0 ∧
      spectralLiouvilleSlope (eta n) (rs n)*(ds n)^3 = 1 := by
    filter_upwards [hφ.tendsto_atTop.eventually hdata] with n hn
    exact ⟨hn.1,hn.2.1,by dsimp only [eta]; positivity,hn.2.2.2.2.1,
      hn.2.2.2.2.2.2.2.1,hn.2.2.2.2.2.2.2.2⟩
  have hs' : ∀ᶠ n in atTop, 0 < rs n ∧ 0 ≤ ds n ∧ 0 ≤ eta n ∧
      homogeneousSpectralLocalizationFrequency h (bs n) (eta n) (os n) (rs n) = 0 ∧
      spectralLiouvilleSlope (eta n) (rs n)*(ds n)^3 = 1 := hs.mono (fun n hn => ⟨hn.1,hn.2.1,hn.2.2.1,hn.2.2.2.2.1,hn.2.2.2.2.2⟩)
  have hd := spectralTurningScale_tendsto eta rs ds hrt
    (hs.mono (fun n hn => ⟨hn.1,hn.2.1,hn.2.2.1,hn.2.2.2.2.2⟩))
  have hu := spectralTurningCoefficient_uniform_limit h bs eta os gs rs ds M 8 (by linarith) hrt hs
  have hw := spectralTurning_regularized_outer_weights h bs eta os gs rs ds M 8 (by linarith) hrt hs
  have hres := spectralTurning_eventual_residual_bound h bs eta os gs rs ds R M hR hM hrt hs'
  have hpos := spectralTurning_oscillatory_uniform (fun n => ell (φ n)) h bs os gs rs ds es M hh hM hrt
    (hφ.tendsto_atTop.eventually hdata)
  let A : ℝ := (25/2)*Real.exp 2
  let C : ℝ := (M+3+(1 : ℝ)⁻¹)*max (1 : ℝ)⁻¹ (M+3)*Real.exp ((1+(M+1))*(M-(-M)))
  let P : ℝ := 25*Real.exp (2304+25/4)
  let K : ℝ := max A (C*A*P)*max A (C*P)/(1/16)
  let J : ℝ := max A (C*P)/(1/16)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hP : 1 ≤ P := by
    have he : 1 ≤ Real.exp (2304+(25/4 : ℝ)) := Real.one_le_exp_iff.mpr (by norm_num)
    dsimp only [P]
    linarith
  refine ⟨q,φ,hφ,hq,K,J,by dsimp only [K,A]; positivity,
    by dsimp only [J,A]; positivity,?_⟩
  filter_upwards [hφ.tendsto_atTop.eventually hq,hφ.tendsto_atTop.eventually hdata,hs,
    hvalue,hw,hres,hpos,(Metric.tendstoUniformlyOn_iff.mp hu) 1 (by norm_num),
    hd.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    hrt.eventually (eventually_ge_atTop (max (16/R) (max (2*R+2) (2*M+2))))]
    with n hqn hdn hsn hvn hwn hrn hpn hun hsmall hlarge
  have hdp : 0 < ds n := by
    apply lt_of_le_of_ne hsn.2.1
    intro he
    have hc := hsn.2.2.2.2.2
    rw [← he] at hc
    norm_num at hc
  have hlargeR := (le_max_left (16/R) (max (2*R+2) (2*M+2))).trans hlarge
  have hlargeRM := (le_max_right (16/R) (max (2*R+2) (2*M+2))).trans hlarge
  have hbigR := (le_max_left (2*R+2) (2*M+2)).trans hlargeRM
  have hbigM := (le_max_right (2*R+2) (2*M+2)).trans hlargeRM
  have hMp : 0 < M := by linarith
  have hMd : ds n*M < rs n/2 := by nlinarith
  let a := rs n-ds n*M
  let z := rs n+ds n*M
  have hRa : R < a := by dsimp only [a]; linarith
  have hzE : z < es n := by dsimp only [z,es,rs] at *; linarith [hdn.2.2.2.2.2.1]
  have ha0 : 0 < a := hR.trans hRa
  have haE : a ≤ es n := by dsimp only [a,z] at *; nlinarith
  have hprod : 16 ≤ rs n*R := by
    have ht := mul_le_mul_of_nonneg_right hlargeR hR.le
    have he : (16/R)*R = 16 := by field_simp
    rwa [he] at ht
  have hF (t : ℝ) (ht : t ∈ Icc R a) :
      0 < (-1)*homogeneousSpectralLocalizationFrequency h (bs n) (eta n) (os n) t := by
    have ht0 := hR.trans_le ht.1
    have htr : t < rs n := by dsimp only [a] at ht; nlinarith [ht.2]
    have he := homogeneousSpectralLocalizationFrequency_strictMono h (bs n) (eta n) (os n)
      hsn.2.2.1 ht0 hsn.1 htr
    rw [hsn.2.2.2.2.1] at he
    linarith
  have hcoef (xi : ℝ) (hxi : xi ∈ Icc (-M) M) :
      ‖spectralTurningCoefficient h (bs n) (eta n) (os n) (gs n) (rs n) (ds n) xi‖ ≤ M+1 := by
    have he : ‖spectralTurningCoefficient h (bs n) (eta n) (os n) (gs n) (rs n) (ds n) xi-(xi : ℂ)‖ ≤ 1 := by
      simpa only [dist_eq_norm,norm_sub_rev] using (hun xi hxi).le
    have hx : ‖(xi : ℂ)‖ ≤ M := by simpa only [Complex.norm_real,Real.norm_eq_abs] using abs_le.mpr hxi
    have hb := norm_add_le (spectralTurningCoefficient h (bs n) (eta n) (os n) (gs n) (rs n) (ds n) xi-(xi : ℂ)) (xi : ℂ)
    rw [sub_add_cancel] at hb
    linarith
  let k := spectralTurningRegularizedWeight h (bs n) (eta n) (os n) (gs n) (ds n)
  have hwl (t : ℝ) (ht : t ∈ Icc R a) : k t =
      Real.sqrt ‖spectralLiouvilleMomentum (-1) h (bs n) (eta n) (os n) (gs n) t‖ :=
    hwn.1 t (hR.trans_le ht.1) ht.2
  have hVp : ContinuousOn (fun t =>
      (homogeneousSpectralLocalizationFrequency h (bs n) (eta n) (os n) t : ℂ)+Complex.I*(gs n : ℂ)) (Icc a (es n)) :=
    (Complex.continuous_ofReal.comp_continuousOn (fun t ht =>
      (homogeneousSpectralLocalizationFrequency_hasDerivAt h (bs n) (eta n) (os n) t
        (ha0.trans_le ht.1)).continuousAt.continuousWithinAt)).add continuousOn_const
  have hqE : q (φ n) (es n) ≠ 0 := by
    intro he
    have hf := hqn.2.2.1
    change spectralScalarFlux (q (φ n) (es n)) = h at hf
    rw [he] at hf
    norm_num [spectralScalarFlux] at hf
    nlinarith [hh]
  have hqa : q (φ n) a ≠ 0 := spectralScalar_ne_zero_of_right a (es n) haE _ hVp _
    hqn.1.continuousOn (fun t ht => hqn.2.2.2 t ⟨hRa.le.trans ht.1.le,ht.2.le⟩) hqE
  have hN : 0 < spectralShellNorm (k a) (q (φ n) a) := by
    have hkp := spectralTurningRegularizedWeight_pos h (bs n) (eta n) (os n) (gs n) (ds n) a hdp
    exact lt_of_le_of_ne (spectralShellNorm_nonneg _ hkp.le _) (fun he =>
      hqa ((spectralShellNorm_eq_zero _ hkp _).mp he.symm))
  have hval : (1/16 : ℝ)*Real.exp ((∫ t in R..a,
      spectralLiouvilleMomentum (-1) h (bs n) (eta n) (os n) (gs n) t).re)*
        spectralShellNorm (k a) (q (φ n) a) ≤ k R*‖(q (φ n) R).1‖ := by
    rw [hwl a ⟨hRa.le,le_rfl⟩,hwl R ⟨le_rfl,hRa.le⟩]
    simpa only [a,bs,eta,os,gs,rs,ds,mul_comm M] using hvn.2
  obtain ⟨Y,W,hYc,hYR,hYD,hW,hdet,hgreen,hext⟩ := spectralTurning_regularized_green_and_extension
    h (bs n) (eta n) (os n) (gs n) (rs n) (ds n) M R (es n) C P hR hdp
    (by linarith) hC hP hRa hzE hcoef le_rfl hF
    (fun t ht => spectralTurning_negative_derivative_small (-1) h (bs n) (eta n) (os n) (gs n)
      (rs n) (ds n) M R t (by norm_num) hsn.2.2.1 hsn.1 hdp hM hR hprod ht.1
      (by simpa only [mul_comm M] using ht.2) hsn.2.2.2.2.1 hsn.2.2.2.2.2)
    (by simpa only [mul_comm M] using hrn) hwl
    (by
      intro v hvc hvD t ht
      have he : rs n+M*ds n = z := by dsimp only [z]; ring
      rw [he] at hpn
      have hz := hwn.2 z le_rfl
      have ht' := hwn.2 t ht.1
      have hp := (hpn v hvc hvD z ⟨le_rfl,hzE.le⟩ t ht ht.1).1
      dsimp only at hp
      rw [← hz,← ht'] at hp
      exact hp)
    (q (φ n)) hqn.1.continuousOn (fun t ht => hqn.2.2.2 t ⟨ht.1.le,ht.2.le⟩) hN hval
  refine ⟨Y,W,hYc,hYR,hYD,hW,hdet,?_,?_⟩
  · intro r hr t ht
    apply (hgreen r hr t ht).trans_eq
    dsimp only [K,A]
    ring
  · intro z r hr
    exact hext z r hr

theorem spectralTurning_outgoing_green_uniform
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
      ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n in atTop,
        let k := spectralTurningRegularizedWeight h (b (φ n))
          ((ell (φ n) : ℝ)*(ell (φ n)+10)) (omega (φ n)) (gamma (φ n)) (d (φ n))
        ∃ (Y : ℝ → ℂ × ℂ) (W : ℂ), Continuous Y ∧ Y R = (0,(k R : ℂ)) ∧
          (∀ t ∈ Icc R (E (φ n)), HasDerivAt Y (spectralScalarField
            ((homogeneousSpectralLocalizationFrequency h (b (φ n))
              ((ell (φ n) : ℝ)*(ell (φ n)+10)) (omega (φ n)) t : ℂ)+
                Complex.I*(gamma (φ n) : ℂ)) (Y t)) t) ∧
          W ≠ 0 ∧ (∀ t ∈ Icc R (E (φ n)), spectralScalarWronskian (Y t) (q (φ n) t) = W) ∧
          ∀ r ∈ Icc R (E (φ n)), ∀ t ∈ Icc R (E (φ n)),
            spectralShellNorm (k r) (spectralScalarGreenState Y (q (φ n)) W r t) ≤ K/(k t) := by
  obtain ⟨q,φ,hφ,hq,K,J,hK,_hJ,hall⟩ := spectralTurning_outgoing_green_extension_uniform
    ell h b omega gamma r₀ d E R hh hR hr₀ hdata
  refine ⟨q,φ,hφ,hq,K,hK,?_⟩
  filter_upwards [hall] with n hn
  obtain ⟨Y,W,hYc,hYR,hYD,hW,hdet,hgreen,_⟩ := hn
  exact ⟨Y,W,hYc,hYR,hYD,hW,hdet,hgreen⟩

end DefocusingNLS

end OAI
