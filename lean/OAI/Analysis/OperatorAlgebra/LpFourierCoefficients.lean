import OAI.Analysis.ModularTheory.FourierTranslation

namespace OAI

/-! Fourier transform commutes with fixed vector coefficients, relating
the scalar inclusion to the vector regular representation. -/

noncomputable section
open MeasureTheory FourierTransform
open scoped SchwartzMap

namespace WeakPureInfiniteness

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma fourier_schwartz_postcomp (L : H →L[ℂ] K) (f : 𝓢(ℝ, H)) :
    𝓕 (f.postcompCLM L) = (𝓕 f).postcompCLM L := by
  ext t
  change 𝓕 (fun x => L (f x)) t = L (𝓕 (f : ℝ → H) t)
  rw [Real.fourier_eq, Real.fourier_eq]
  have hi := (Real.fourierIntegral_convergent_iff t).mpr
    (f.integrable (μ := (volume : Measure ℝ)))
  rw [← L.integral_comp_comm hi]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [Circle.smul_def, map_smul]

omit [CompleteSpace H] [CompleteSpace K] in
lemma compLp_schwartz (L : H →L[ℂ] K) (f : 𝓢(ℝ, H)) :
    L.compLpL 2 volume (f.toLp 2) = (f.postcompCLM L).toLp 2 := by
  apply Lp.ext
  filter_upwards [L.coeFn_compLpL (p := 2) (μ := volume) (f.toLp 2),
    f.coeFn_toLp 2 volume, (f.postcompCLM L).coeFn_toLp 2 volume] with t h₁ h₂ h₃
  rw [h₁, h₂, h₃, SchwartzMap.postcompCLM_apply]

lemma fourier_compLp (L : H →L[ℂ] K) (f : Lp H 2 (volume : Measure ℝ)) :
    𝓕 (L.compLpL 2 volume f) = L.compLpL 2 volume (𝓕 f) := by
  have hd : DenseRange (SchwartzMap.toLpCLM ℝ H 2 (volume : Measure ℝ)) :=
    SchwartzMap.denseRange_toLpCLM ENNReal.ofNat_ne_top
  refine hd.induction_on f ?_ ?_
  · exact isClosed_eq
      ((Lp.fourierTransformₗᵢ ℝ K).continuous.comp (L.compLpL 2 volume).continuous)
      ((L.compLpL 2 volume).continuous.comp (Lp.fourierTransformₗᵢ ℝ H).continuous)
  · intro g
    change 𝓕 (L.compLpL 2 volume (g.toLp 2)) = L.compLpL 2 volume (𝓕 (g.toLp 2))
    rw [compLp_schwartz, SchwartzMap.toLp_fourier_eq,
      SchwartzMap.toLp_fourier_eq, compLp_schwartz, fourier_schwartz_postcomp]

lemma fourierInv_compLp (L : H →L[ℂ] K) (f : Lp H 2 (volume : Measure ℝ)) :
    𝓕⁻ (L.compLpL 2 volume f) = L.compLpL 2 volume (𝓕⁻ f) := by
  apply (Lp.fourierTransformₗᵢ ℝ K).injective
  change 𝓕 (𝓕⁻ (L.compLpL 2 volume f)) = 𝓕 (L.compLpL 2 volume (𝓕⁻ f))
  rw [fourier_fourierInv_eq, fourier_compLp, fourier_fourierInv_eq]

end WeakPureInfiniteness

end

end OAI
