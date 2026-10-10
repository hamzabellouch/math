import OAI.Analysis.ModularTheory.TomitaTime

namespace OAI

/-! A finite-weight approximate identity whose GNS vector is the explicit
time-domain Gaussian used in the Tomita calculation. The factor 2π is fixed
by the Fourier convention, rather than absorbed into an informal notation. -/

noncomputable section
open MeasureTheory Filter FourierTransform
open scoped Topology ENNReal

namespace WeakPureInfiniteness
open BoundedRecovery

def modularFrequencyGaussian (n : ℕ) : BoundedContinuousFunction ℝ ℂ :=
  (modularGaussian n).compContinuous ⟨fun ω => 2 * Real.pi * ω, by fun_prop⟩

lemma modularFrequencyGaussian_norm (n : ℕ) (ω : ℝ) :
    ‖modularFrequencyGaussian n ω‖ ≤ 1 := modularGaussian_norm_le n _

lemma modularFrequencyGaussian_tendsto (ω : ℝ) :
    Tendsto (fun n => modularFrequencyGaussian n ω) atTop (𝓝 1) :=
  modularGaussian_tendsto _

lemma modularTomitaKernel_fourier_scalar (n : ℕ) (ω : ℝ) :
    𝓕 (modularTomitaKernel n) ω = modularWeightedFunction (modularFrequencyGaussian n) ω := by
  have h := weightedGaussianKernel_fourier ((n + 1 : ℝ) / 4) (by positivity)
    (2 * Real.pi * ω)
  have he : 𝓕 (modularTomitaKernel n) ω =
      ∫ t : ℝ, modularTomitaKernel n t * spectralCharacter (-(2 * Real.pi * ω)) t := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    apply integral_congr_ae
    filter_upwards [] with t
    change Complex.exp _ * _ = _ * Complex.exp _
    rw [mul_comm]
    congr 2
    push_cast
    ring
  rw [he]
  change (∫ t : ℝ, weightedGaussianKernel ((n + 1 : ℝ) / 4) t * _) = _
  rw [h]
  change Complex.exp _ =
    (Real.exp (-(2 * Real.pi * ω) ^ 2 / (n + 1)) : ℂ) *
      (Real.exp (Real.pi * ω) : ℂ)
  rw [← Complex.ofReal_mul, ← Real.exp_add, Complex.ofReal_exp]
  congr 1
  push_cast
  have hn : (n : ℂ) + 1 ≠ 0 := by
    exact_mod_cast (show (n : ℝ) + 1 ≠ 0 by positivity)
  field_simp
  ring

lemma modularFrequencyGaussian_integrable (n : ℕ) :
    Integrable (fun ω : ℝ => ‖modularFrequencyGaussian n ω‖ ^ 2 *
      Real.exp (2 * Real.pi * ω)) := by
  have hf : MemLp (modularWeightedFunction (modularFrequencyGaussian n)) 2
      (volume : Measure ℝ) := by
    have hmem : MemLp ((𝓕 (modularTomitaKernelVector n) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) 2
        (volume : Measure ℝ) := Lp.memLp _
    refine (memLp_congr_ae ?_).mp hmem
    filter_upwards [fourier_toLp_ae_of_integrable (modularTomitaKernel n)
      (modularTomitaKernel_integrable n) (modularTomitaKernel_memLp n)] with ω hω
    change (𝓕 (modularTomitaKernelVector n) : Lp ℂ 2 (volume : Measure ℝ)) ω = _ at hω
    rw [hω, modularTomitaKernel_fourier_scalar]
  have hi := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  simpa only [modularWeightedFunction_norm_sq] using hi

lemma modularFrequencyGaussian_weightedVector (n : ℕ) :
    modularWeightedVector (modularFrequencyGaussian n) (modularFrequencyGaussian_integrable n) =
      𝓕 (modularTomitaKernelVector n) := by
  apply Lp.ext
  filter_upwards [modularWeightedVector_ae (modularFrequencyGaussian n)
    (modularFrequencyGaussian_integrable n),
    fourier_toLp_ae_of_integrable (modularTomitaKernel n)
      (modularTomitaKernel_integrable n) (modularTomitaKernel_memLp n)] with ω hv hF
  change (𝓕 (modularTomitaKernelVector n) : Lp ℂ 2 (volume : Measure ℝ)) ω = _ at hF
  rw [hv, hF, modularTomitaKernel_fourier_scalar]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma modularFrequencyGaussian_weightVector (S : StandardModularData H) (n : ℕ) :
    modularWeightVector S (modularTranslationCalculus (modularFrequencyGaussian n))
      (modularTranslationCalculus_mem S _)
      (modularTranslationCalculus_finite S _ (modularFrequencyGaussian_integrable n)) =
        modularScalarInclusion volume S (modularTomitaKernelVector n) := by
  rw [modularTranslationCalculus_weightVector S _ (modularFrequencyGaussian_integrable n),
    modularFrequencyGaussian_weightedVector]
  change modularScalarInclusion volume S (𝓕⁻ (𝓕 (modularTomitaKernelVector n))) = _
  rw [fourierInv_fourier_eq]

lemma modularFrequencyGaussian_strong (f : Lp H 2 (volume : Measure ℝ)) :
    Tendsto (fun n => modularTranslationCalculus (modularFrequencyGaussian n) f)
      atTop (𝓝 f) := by
  have h := vectorLpRepresentation_strong modularFrequencyGaussian (fun _ => 1)
    (by fun_prop) 1 zero_le_one modularFrequencyGaussian_norm (by simp)
    modularFrequencyGaussian_tendsto (𝓕 f)
  have he : boundedVectorLp (H := H) volume (fun _ => 1) (by fun_prop) 1
      (by simp) = 1 := by
    apply ContinuousLinearMap.ext
    intro v
    apply Lp.ext
    filter_upwards [boundedVectorLp_ae volume (fun _ => 1) (by fun_prop) 1 (by simp) v]
      with t ht
    change _ = v t
    simpa only [one_smul] using ht
  have hf := (Lp.fourierTransformₗᵢ ℝ H).symm.continuous.continuousAt.tendsto.comp h
  simp only [he, one_apply_eq_self] at hf
  change Tendsto (fun n => modularTranslationCalculus (modularFrequencyGaussian n) f)
    atTop (𝓝 (𝓕⁻ (𝓕 f))) at hf
  simpa only [fourierInv_fourier_eq] using hf

end WeakPureInfiniteness

end

end OAI
