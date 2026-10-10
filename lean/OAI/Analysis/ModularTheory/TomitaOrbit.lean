import OAI.Analysis.ModularTheory.WeightedFourierBound

namespace OAI

/-! Removing the compact spectral cutoff from the Gaussian orbit formula.
The orbit integral is a bounded operator on the actual Hilbert space, so
its identity on the dense compact spectral vectors determines it everywhere. -/

noncomputable section
open MeasureTheory FourierTransform Filter
open scoped Topology

namespace WeakPureInfiniteness
open BoundedRecovery

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def modularTomitaFrequencyKernel (n : ℕ) (ω t : ℝ) : ℂ :=
  modularTomitaKernel n t * spectralCharacter (-(2 * Real.pi * ω)) t

lemma modularTomitaFrequencyKernel_integrable (n : ℕ) (ω : ℝ) :
    Integrable (modularTomitaFrequencyKernel n ω) := by
  apply (modularTomitaKernel_integrable n).norm.mono'
    ((modularTomitaKernel_integrable n).aestronglyMeasurable.mul
      (spectralCharacter (-(2 * Real.pi * ω))).continuous.aestronglyMeasurable)
  exact ae_of_all _ (fun t => by
    change ‖modularTomitaKernel n t * spectralCharacter (-(2 * Real.pi * ω)) t‖ ≤ _
    simp only [norm_mul, spectralCharacter_norm, mul_one, le_refl])

def modularTomitaOrbitOperator (D : RealSpectralCalculus H) (n : ℕ) (ω : ℝ) : H →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun := fun x => ∫ t : ℝ, modularTomitaFrequencyKernel n ω t • D.unitary (-t) x
      map_add' := by
        intro x y
        simp only [map_add, smul_add]
        exact integral_add
          (integrable_spectral_orbit D _ (modularTomitaFrequencyKernel_integrable n ω) x)
          (integrable_spectral_orbit D _ (modularTomitaFrequencyKernel_integrable n ω) y)
      map_smul' := by
        intro c x
        simp only [map_smul, RingHom.id_apply, smul_comm _ c, integral_smul] }
    (∫ t : ℝ, ‖modularTomitaFrequencyKernel n ω t‖)
    (by
      intro x
      calc
        _ ≤ ∫ t : ℝ, ‖modularTomitaFrequencyKernel n ω t • D.unitary (-t) x‖ :=
          norm_integral_le_integral_norm _
        _ = (∫ t : ℝ, ‖modularTomitaFrequencyKernel n ω t‖) * ‖x‖ := by
          simp only [norm_smul, D.norm_unitary_apply, integral_mul_const])

lemma modularTomitaOrbitOperator_fourier (D : RealSpectralCalculus H)
    (n : ℕ) (ω : ℝ) (x : H) :
    modularTomitaOrbitOperator D n ω x =
      𝓕 (fun t => modularTomitaKernel n t • D.unitary (-t) x) ω := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards [] with t
  change (modularTomitaKernel n t * spectralCharacter (-(2 * Real.pi * ω)) t) • _ = _
  rw [smul_smul, mul_comm]
  congr 2
  change Complex.exp _ = Complex.exp _
  congr 1
  push_cast
  ring

lemma modularTomitaOrbitOperator_eq (D : RealSpectralCalculus H) (n : ℕ) (ω : ℝ) :
    modularTomitaOrbitOperator D n ω =
      (Real.exp (Real.pi * ω) : ℂ) •
        D.calculus (modularShiftedHalfGaussian n (2 * Real.pi * ω)) := by
  have h : (fun x => modularTomitaOrbitOperator D n ω x) =
      (fun x => ((Real.exp (Real.pi * ω) : ℂ) •
        D.calculus (modularShiftedHalfGaussian n (2 * Real.pi * ω))) x) := by
    apply Continuous.ext_on D.nondegenerate
      (modularTomitaOrbitOperator D n ω).continuous
      ((Real.exp (Real.pi * ω) : ℂ) •
        D.calculus (modularShiftedHalfGaussian n (2 * Real.pi * ω))).continuous
    rintro _ ⟨χ, hχ, x, rfl⟩
    rw [modularTomitaOrbitOperator_fourier,
      fourier_spectral_orbit D _ (modularTomitaKernel_integrable n) χ hχ,
      modularTomitaKernel_calculus D n _ χ hχ]
    have he : (2 * Real.pi * ω) / 2 = Real.pi * ω := by ring
    simp only [he, smul_apply]
  exact ContinuousLinearMap.ext (fun x => congrFun h x)

lemma modularTomitaKernel_fourier_all (D : RealSpectralCalculus H)
    (n : ℕ) (ω : ℝ) (x : H) :
    𝓕 (fun t => modularTomitaKernel n t • D.unitary (-t) x) ω =
      (Real.exp (Real.pi * ω) : ℂ) •
        D.calculus (modularShiftedHalfGaussian n (2 * Real.pi * ω)) x := by
  rw [← modularTomitaOrbitOperator_fourier, modularTomitaOrbitOperator_eq]
  rfl

lemma modularTomitaKernel_fourier_limit_all (D : RealSpectralCalculus H)
    {x y : H} (hxy : (x, y) ∈ D.halfGraph) (ω : ℝ) :
    Tendsto (fun n => 𝓕 (fun t => modularTomitaKernel n t • D.unitary (-t) x) ω)
      atTop (𝓝 ((Real.exp (Real.pi * ω) : ℂ) • y)) := by
  simp_rw [modularTomitaKernel_fourier_all]
  exact (modularShiftedHalfGaussian_strong D hxy _).const_smul _

lemma modularTomitaKernel_fourier_norm_all (D : RealSpectralCalculus H)
    {x y : H} (hxy : (x, y) ∈ D.halfGraph) (n : ℕ) (ω : ℝ) :
    ‖𝓕 (fun t => modularTomitaKernel n t • D.unitary (-t) x) ω‖ ≤
      Real.exp (Real.pi * ω) * ‖y‖ := by
  rw [modularTomitaKernel_fourier_all, norm_smul]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left (modularShiftedHalfGaussian_norm D hxy _ n)
    (Real.exp_pos _).le

end WeakPureInfiniteness

end

end OAI
