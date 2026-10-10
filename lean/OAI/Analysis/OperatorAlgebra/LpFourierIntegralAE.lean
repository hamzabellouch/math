import OAI.Analysis.OperatorAlgebra.LpFourierIntegral

namespace OAI

/-! The classical integral represents the L² Fourier transform on L¹∩L².
The proof tests the two locally integrable functions against compact smooth
functions, using the existing distributional Fourier compatibility. -/

noncomputable section
open MeasureTheory FourierTransform
open scoped ContDiff

namespace WeakPureInfiniteness

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma fourier_toLp_ae_of_integrable (f : ℝ → H) (hi : Integrable f)
    (hf : MemLp f 2 (volume : Measure ℝ)) :
    (𝓕 (hf.toLp f) : Lp H 2 (volume : Measure ℝ)) =ᵐ[volume] 𝓕 f := by
  have hc : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hi
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp (𝓕 (hf.toLp f))).locallyIntegrable (by norm_num)) hc.locallyIntegrable
  intro g hg hgc
  have hgc' : HasCompactSupport (Complex.ofRealCLM ∘ g) := hgc.comp_left rfl
  have hg' : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
  let φ : SchwartzMap ℝ ℂ := hgc'.toSchwartzMap hg'
  have hd := congrArg (fun T : TemperedDistribution ℝ H => T φ)
    (Lp.fourier_toTemperedDistribution_eq (hf.toLp f))
  simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply] at hd
  calc
    (∫ t : ℝ, g t • (𝓕 (hf.toLp f) : Lp H 2 (volume : Measure ℝ)) t) =
        ∫ t : ℝ, φ t • (𝓕 (hf.toLp f) : Lp H 2 (volume : Measure ℝ)) t := by
      apply integral_congr_ae
      exact ae_of_all _ (fun t => by change g t • _ = (g t : ℂ) • _; simp)
    _ = ∫ t : ℝ, (𝓕 φ) t • (hf.toLp f) t := hd.symm
    _ = ∫ t : ℝ, (𝓕 φ) t • f t := by
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp] with t ht
      rw [ht]
    _ = ∫ t : ℝ, φ t • (𝓕 f) t := by
      simpa using! VectorFourier.integral_fourierIntegral_smul_eq_flip
        (L := innerₗ ℝ) Real.continuous_fourierChar continuous_inner φ.integrable hi
    _ = ∫ t : ℝ, g t • (𝓕 f) t := by
      apply integral_congr_ae
      exact ae_of_all _ (fun t => by change (g t : ℂ) • _ = g t • _; simp)

  rfl

end WeakPureInfiniteness

end

end OAI
