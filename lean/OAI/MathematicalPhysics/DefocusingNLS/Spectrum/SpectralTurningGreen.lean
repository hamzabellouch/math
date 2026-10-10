import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralThreeRegionGreen
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLiouvilleForbiddenBounds
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLiouvilleActionOrder
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningRegularizedTransfer

namespace OAI

/-! Extend the actual outgoing scalar Green kernel to both sides of the
turn, in the continuous regularized frequency norm. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralTurning_regularized_green_and_extension
    (h b eta omega gamma r₀ d M R E C P : ℝ)
    (hR : 0 < R) (hd : 0 < d) (hM : 0 ≤ M) (hC : 0 ≤ C) (hP : 1 ≤ P)
    (hRa : R < r₀-d*M) (hbE : r₀+d*M < E)
    (hcoef : ∀ xi ∈ Icc (-M) M,
      ‖spectralTurningCoefficient h b eta omega gamma r₀ d xi‖ ≤ M+1)
    (hCbound : (M+3+(1 : ℝ)⁻¹)*max (1 : ℝ)⁻¹ (M+3)*
      Real.exp ((1+(M+1))*(M-(-M))) ≤ C)
    (hF : ∀ t ∈ Icc R (r₀-d*M),
      0 < (-1)*homogeneousSpectralLocalizationFrequency h b eta omega t)
    (hsmall : ∀ t ∈ Icc R (r₀-d*M), |spectralLiouvilleSlope eta t| ≤
      2*‖spectralLiouvilleMomentum (-1) h b eta omega gamma t‖^3)
    (hJ : (∫ t in R..(r₀-d*M), (25/4 : ℝ)*
      ‖spectralLiouvilleResidual (-1) h b eta omega gamma t‖/
        ‖spectralLiouvilleMomentum (-1) h b eta omega gamma t‖) ≤ 2)
    (hweight : ∀ t ∈ Icc R (r₀-d*M),
      spectralTurningRegularizedWeight h b eta omega gamma d t =
        Real.sqrt ‖spectralLiouvilleMomentum (-1) h b eta omega gamma t‖)
    (hpos : ∀ q : ℝ → ℂ × ℂ, ContinuousOn q (Icc (r₀+d*M) E) →
      (∀ t ∈ Ioo (r₀+d*M) E, HasDerivAt q (spectralScalarField
        ((homogeneousSpectralLocalizationFrequency h b eta omega t : ℂ)+
          Complex.I*(gamma : ℂ)) (q t)) t) →
      ∀ t ∈ Icc (r₀+d*M) E,
        spectralShellNorm (spectralTurningRegularizedWeight h b eta omega gamma d t) (q t) ≤
          P*spectralShellNorm (spectralTurningRegularizedWeight h b eta omega gamma d (r₀+d*M))
            (q (r₀+d*M)))
    (U : ℝ → ℂ × ℂ) (hUc : ContinuousOn U (Icc R E))
    (hUD : ∀ t ∈ Ioo R E, HasDerivAt U (spectralScalarField
      ((homogeneousSpectralLocalizationFrequency h b eta omega t : ℂ)+
        Complex.I*(gamma : ℂ)) (U t)) t)
    (hN : 0 < spectralShellNorm (spectralTurningRegularizedWeight h b eta omega gamma d (r₀-d*M))
      (U (r₀-d*M)))
    (hvalue : (1/16 : ℝ)*Real.exp ((∫ t in R..(r₀-d*M),
      spectralLiouvilleMomentum (-1) h b eta omega gamma t).re)*
        spectralShellNorm (spectralTurningRegularizedWeight h b eta omega gamma d (r₀-d*M))
          (U (r₀-d*M)) ≤ spectralTurningRegularizedWeight h b eta omega gamma d R*‖(U R).1‖) :
    let k := spectralTurningRegularizedWeight h b eta omega gamma d
    let A := (25/2 : ℝ)*Real.exp 2
    ∃ (Y : ℝ → ℂ × ℂ) (W : ℂ), Continuous Y ∧ Y R = (0,(k R : ℂ)) ∧
      (∀ t ∈ Icc R E, HasDerivAt Y (spectralScalarField
        ((homogeneousSpectralLocalizationFrequency h b eta omega t : ℂ)+
          Complex.I*(gamma : ℂ)) (Y t)) t) ∧
      W ≠ 0 ∧ (∀ t ∈ Icc R E, spectralScalarWronskian (Y t) (U t) = W) ∧
      (∀ r ∈ Icc R E, ∀ t ∈ Icc R E,
        spectralShellNorm (k r) (spectralScalarGreenState Y U W r t) ≤
          max A (C*A*P)*max A (C*P)/((1/16)*k t)) ∧
      ∀ z : ℂ, ∀ r ∈ Icc R E,
        spectralShellNorm (k r) ((z/(U R).1) • U r) ≤ (max A (C*P)/(1/16))*k R*‖z‖ := by
  let a := r₀-d*M
  let z := r₀+d*M
  let k := spectralTurningRegularizedWeight h b eta omega gamma d
  let V := fun t => (homogeneousSpectralLocalizationFrequency h b eta omega t : ℂ)+Complex.I*(gamma : ℂ)
  let H := fun r => (∫ t in r..a, spectralLiouvilleMomentum (-1) h b eta omega gamma t).re
  let A := (25/2 : ℝ)*Real.exp 2
  have haz : a ≤ z := by dsimp only [a,z]; nlinarith
  have hRE : R ≤ E := hRa.le.trans (haz.trans hbE.le)
  have hV : ContinuousOn V (Icc R E) :=
    (Complex.continuous_ofReal.comp_continuousOn (fun t ht =>
      (homogeneousSpectralLocalizationFrequency_hasDerivAt h b eta omega t
        (hR.trans_le ht.1)).continuousAt.continuousWithinAt)).add continuousOn_const
  have hk (t : ℝ) (_ht : t ∈ Icc R E) : 0 < k t :=
    spectralTurningRegularizedWeight_pos h b eta omega gamma d t hd
  apply spectralScalar_three_region_green_and_extension R a z E A C P (1/16) hRa.le haz hbE.le
    (by dsimp only [A]; positivity) hC hP (by norm_num) V k H hV hk
    (spectralLiouville_action_antitone h b eta omega gamma R a hR hF)
    (by dsimp only [H]; simp only [intervalIntegral.integral_same,Complex.zero_re]) U hUc hUD hN hvalue
  · intro q hq hqD t ht
    have hsub : Icc R a ⊆ Icc R E := Icc_subset_Icc le_rfl (haz.trans hbE.le)
    have hb := spectralLiouville_forbidden_bounds h b eta omega gamma R a hR hRa.le hF hsmall
      q (hq.mono hsub) (fun s hs => hqD s ⟨hs.1,hs.2.trans_le (haz.trans hbE.le)⟩) t ht
    have he : Real.exp (∫ s in R..a, (25/4 : ℝ)*
        ‖spectralLiouvilleResidual (-1) h b eta omega gamma s‖/
          ‖spectralLiouvilleMomentum (-1) h b eta omega gamma s‖) ≤ Real.exp 2 :=
      Real.exp_le_exp.mpr hJ
    have hkt := hweight t ht
    have hkR := hweight R ⟨le_rfl,hRa.le⟩
    have hka := hweight a ⟨hRa.le,le_rfl⟩
    change k t = _ at hkt
    change k R = _ at hkR
    change k a = _ at hka
    dsimp only at hb
    rw [← hkt,← hkR,← hka] at hb
    have hNR := spectralShellNorm_nonneg (k R) (hk R ⟨le_rfl,hRE⟩).le (q R)
    have hNa := spectralShellNorm_nonneg (k a) (hk a ⟨hRa.le,haz.trans hbE.le⟩).le (q a)
    have he1 : (25/4 : ℝ)*Real.exp (∫ s in R..a, (25/4 : ℝ)*
        ‖spectralLiouvilleResidual (-1) h b eta omega gamma s‖/
          ‖spectralLiouvilleMomentum (-1) h b eta omega gamma s‖) ≤ A := by
      calc
        _ ≤ (25/4 : ℝ)*Real.exp 2 := mul_le_mul_of_nonneg_left he (by norm_num)
        _ ≤ A := by dsimp only [A]; nlinarith [Real.exp_pos (2 : ℝ)]
    have he2 : (25/2 : ℝ)*Real.exp (∫ s in R..a, (25/4 : ℝ)*
        ‖spectralLiouvilleResidual (-1) h b eta omega gamma s‖/
          ‖spectralLiouvilleMomentum (-1) h b eta omega gamma s‖) ≤ A :=
      mul_le_mul_of_nonneg_left he (by norm_num)
    constructor
    · exact hb.1.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right he1 (Real.exp_pos (H R-H t)).le) hNR)
    · exact hb.2.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right he2 (Real.exp_pos (H t)).le) hNa)
  · intro q hq hqD t ht
    have hsub : Icc a z ⊆ Icc R E := Icc_subset_Icc hRa.le hbE.le
    have hb := (spectralTurning_regularized_physical_transfer h b eta omega gamma r₀ d M
      hd hM hcoef q (hq.mono hsub)
      (fun s hs => hqD s ⟨hRa.trans_le hs.1,hs.2.trans_lt hbE⟩)
      a t ⟨le_rfl,haz⟩ ht ht.1).1
    exact hb.trans (mul_le_mul_of_nonneg_right hCbound (spectralShellNorm_nonneg _ (hk a ⟨hRa.le,haz.trans hbE.le⟩).le _))
  · intro q hq hqD t ht
    exact hpos q (hq.mono (Icc_subset_Icc (hRa.le.trans haz) le_rfl))
      (fun s hs => hqD s ⟨(hRa.le.trans haz).trans_lt hs.1,hs.2⟩) t ht

theorem spectralTurning_regularized_green
    (h b eta omega gamma r₀ d M R E C P : ℝ)
    (hR : 0 < R) (hd : 0 < d) (hM : 0 ≤ M) (hC : 0 ≤ C) (hP : 1 ≤ P)
    (hRa : R < r₀-d*M) (hbE : r₀+d*M < E)
    (hcoef : ∀ xi ∈ Icc (-M) M,
      ‖spectralTurningCoefficient h b eta omega gamma r₀ d xi‖ ≤ M+1)
    (hCbound : (M+3+(1 : ℝ)⁻¹)*max (1 : ℝ)⁻¹ (M+3)*
      Real.exp ((1+(M+1))*(M-(-M))) ≤ C)
    (hF : ∀ t ∈ Icc R (r₀-d*M),
      0 < (-1)*homogeneousSpectralLocalizationFrequency h b eta omega t)
    (hsmall : ∀ t ∈ Icc R (r₀-d*M), |spectralLiouvilleSlope eta t| ≤
      2*‖spectralLiouvilleMomentum (-1) h b eta omega gamma t‖^3)
    (hJ : (∫ t in R..(r₀-d*M), (25/4 : ℝ)*
      ‖spectralLiouvilleResidual (-1) h b eta omega gamma t‖/
        ‖spectralLiouvilleMomentum (-1) h b eta omega gamma t‖) ≤ 2)
    (hweight : ∀ t ∈ Icc R (r₀-d*M),
      spectralTurningRegularizedWeight h b eta omega gamma d t =
        Real.sqrt ‖spectralLiouvilleMomentum (-1) h b eta omega gamma t‖)
    (hpos : ∀ q : ℝ → ℂ × ℂ, ContinuousOn q (Icc (r₀+d*M) E) →
      (∀ t ∈ Ioo (r₀+d*M) E, HasDerivAt q (spectralScalarField
        ((homogeneousSpectralLocalizationFrequency h b eta omega t : ℂ)+
          Complex.I*(gamma : ℂ)) (q t)) t) →
      ∀ t ∈ Icc (r₀+d*M) E,
        spectralShellNorm (spectralTurningRegularizedWeight h b eta omega gamma d t) (q t) ≤
          P*spectralShellNorm (spectralTurningRegularizedWeight h b eta omega gamma d (r₀+d*M))
            (q (r₀+d*M)))
    (U : ℝ → ℂ × ℂ) (hUc : ContinuousOn U (Icc R E))
    (hUD : ∀ t ∈ Ioo R E, HasDerivAt U (spectralScalarField
      ((homogeneousSpectralLocalizationFrequency h b eta omega t : ℂ)+
        Complex.I*(gamma : ℂ)) (U t)) t)
    (hN : 0 < spectralShellNorm (spectralTurningRegularizedWeight h b eta omega gamma d (r₀-d*M))
      (U (r₀-d*M)))
    (hvalue : (1/16 : ℝ)*Real.exp ((∫ t in R..(r₀-d*M),
      spectralLiouvilleMomentum (-1) h b eta omega gamma t).re)*
        spectralShellNorm (spectralTurningRegularizedWeight h b eta omega gamma d (r₀-d*M))
          (U (r₀-d*M)) ≤ spectralTurningRegularizedWeight h b eta omega gamma d R*‖(U R).1‖) :
    let k := spectralTurningRegularizedWeight h b eta omega gamma d
    let A := (25/2 : ℝ)*Real.exp 2
    ∃ (Y : ℝ → ℂ × ℂ) (W : ℂ), Continuous Y ∧ Y R = (0,(k R : ℂ)) ∧
      (∀ t ∈ Icc R E, HasDerivAt Y (spectralScalarField
        ((homogeneousSpectralLocalizationFrequency h b eta omega t : ℂ)+
          Complex.I*(gamma : ℂ)) (Y t)) t) ∧
      W ≠ 0 ∧ (∀ t ∈ Icc R E, spectralScalarWronskian (Y t) (U t) = W) ∧
      ∀ r ∈ Icc R E, ∀ t ∈ Icc R E,
        spectralShellNorm (k r) (spectralScalarGreenState Y U W r t) ≤
          max A (C*A*P)*max A (C*P)/((1/16)*k t) := by
  obtain ⟨Y,W,hYc,hYR,hYD,hW,hdet,hgreen,_⟩ :=
    spectralTurning_regularized_green_and_extension h b eta omega gamma r₀ d M R E C P
      hR hd hM hC hP hRa hbE hcoef hCbound hF hsmall hJ hweight hpos U hUc hUD hN hvalue
  exact ⟨Y,W,hYc,hYR,hYD,hW,hdet,hgreen⟩

end DefocusingNLS

end OAI
