import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLiouvilleOscillatoryTransfer

namespace OAI

/-! Every subinterval of the oscillatory region has the same transfer bound.
The phase and residual integrals are nonnegative and therefore restrict. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralLiouville_oscillatory_subinterval (h b eta omega gamma R E A B : ℝ)
    (hR : 0 < R) (hRE : R ≤ E)
    (hF : ∀ t ∈ Icc R E, 0 < homogeneousSpectralLocalizationFrequency h b eta omega t)
    (hsmall : ∀ t ∈ Icc R E, |spectralLiouvilleSlope eta t| ≤
      2*‖spectralLiouvilleMomentum 1 h b eta omega gamma t‖^3)
    (hA : (∫ t in R..E, 1/Real.sqrt (homogeneousSpectralLocalizationFrequency h b eta omega t)) ≤ A)
    (hB : (∫ t in R..E, ‖spectralLiouvilleResidual 1 h b eta omega gamma t‖/
      ‖spectralLiouvilleMomentum 1 h b eta omega gamma t‖) ≤ B)
    (r t : ℝ) (hr : r ∈ Icc R E) (ht : t ∈ Icc R E) (hrt : r ≤ t)
    (q : ℝ → ℂ × ℂ) (hq : ContinuousOn q (Icc R E))
    (hODE : ∀ s ∈ Ioo R E, HasDerivAt q
      (spectralScalarField ((homogeneousSpectralLocalizationFrequency h b eta omega s : ℂ)+
        Complex.I*(gamma : ℂ)) (q s)) s) :
    let k := fun s => Real.sqrt ‖spectralLiouvilleMomentum 1 h b eta omega gamma s‖
    let C := (25/4 : ℝ)*Real.exp (|gamma| *A+(25/4)*B)
    spectralShellNorm (k t) (q t) ≤ C*spectralShellNorm (k r) (q r) ∧
      spectralShellNorm (k r) (q r) ≤ (2*C)*spectralShellNorm (k t) (q t) := by
  have hsub : Icc r t ⊆ Icc R E := Icc_subset_Icc hr.1 ht.2
  have hFC : ContinuousOn (homogeneousSpectralLocalizationFrequency h b eta omega) (Icc R E) :=
    fun s hs => (homogeneousSpectralLocalizationFrequency_hasDerivAt h b eta omega s
      (hR.trans_le hs.1)).continuousAt.continuousWithinAt
  have hcA : ContinuousOn (fun s => 1/Real.sqrt
      (homogeneousSpectralLocalizationFrequency h b eta omega s)) (Icc R E) :=
    continuousOn_const.div (Real.continuous_sqrt.comp_continuousOn hFC)
      (fun s hs => (Real.sqrt_pos.mpr (hF s hs)).ne')
  have hcB := (spectralLiouvilleResidual_continuousOn 1 h b eta omega gamma R E
    (by norm_num) hR (by simpa only [one_mul] using hF)).2
  have hAsub : (∫ s in r..t, 1/Real.sqrt (homogeneousSpectralLocalizationFrequency h b eta omega s)) ≤ A :=
    (intervalIntegral.integral_mono_interval hr.1 hrt ht.2
      (Filter.Eventually.of_forall (fun s => by positivity))
      (hcA.intervalIntegrable_of_Icc hRE)).trans hA
  have hBsub : (∫ s in r..t, ‖spectralLiouvilleResidual 1 h b eta omega gamma s‖/
      ‖spectralLiouvilleMomentum 1 h b eta omega gamma s‖) ≤ B :=
    (intervalIntegral.integral_mono_interval hr.1 hrt ht.2
      (Filter.Eventually.of_forall (fun s => by positivity))
      (hcB.intervalIntegrable_of_Icc hRE)).trans hB
  exact spectralLiouville_oscillatory_endpoint h b eta omega gamma r t A B
    (hR.trans_le hr.1) hrt (fun s hs => hF s (hsub hs))
    (fun s hs => hsmall s (hsub hs)) hAsub hBsub q (hq.mono hsub)
    (fun s hs => hODE s ⟨hr.1.trans_lt hs.1,hs.2.trans_le ht.2⟩)

end DefocusingNLS

end OAI
