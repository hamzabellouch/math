import OAI.MeasureTheory.Falconer.Estimates.SpatialPlancherel

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set Filter
open scoped FourierTransform SchwartzMap ComplexInnerProductSpace

 theorem integral_sq_norm_toLp (f : ℝ → ℂ) (hf : MemLp f 2 volume) :
    (∫ x, ‖f x‖^2) = ‖hf.toLp f‖^2 := by
  have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (hf.toLp f)
  rw [L2.inner_def] at h
  simp only [inner_self_eq_norm_sq_to_K] at h
  norm_cast at h
  calc
    _ = ∫ x, ‖(hf.toLp f) x‖^2 := integral_congr_ae
      (hf.coeFn_toLp.symm.mono (fun x hx => by dsimp only; rw [hx]))
    _ = _ := h

 theorem integrable_fourier_memLp_two (f : ℝ → ℂ) (h1 : Integrable f)
    (h2 : MemLp f 2 volume) : MemLp (𝓕 f) 2 volume :=
  MemLp.ae_eq (fourier_L2_ae f h1 h2) (Lp.memLp (𝓕 (h2.toLp f) : Lp ℂ 2 volume))

 theorem integrable_fourier_plancherel (f : ℝ → ℂ) (h1 : Integrable f)
    (h2 : MemLp f 2 volume) : (∫ x, ‖𝓕 f x‖^2) = ∫ x, ‖f x‖^2 := by
  have he := fourier_L2_ae f h1 h2
  calc
    _ = ∫ x, ‖(𝓕 (h2.toLp f) : Lp ℂ 2 volume) x‖^2 :=
      integral_congr_ae (he.symm.mono (fun x hx => by dsimp only; rw [hx]))
    _ = ‖𝓕 (h2.toLp f)‖^2 := by
      have h := integral_sq_norm_toLp _ (Lp.memLp (𝓕 (h2.toLp f)))
      simpa only [Lp.toLp_coeFn] using h
    _ = _ := by rw [Lp.norm_fourier_eq, integral_sq_norm_toLp f h2]

 theorem sourceInverseKernel_continuous (f : ℝ → ℂ) (hf : Integrable f) :
    Continuous (sourceInverseKernel f) := by
  exact (continuous_const (y := (2*Real.pi)⁻¹)).smul ((VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar (innerSL ℝ).continuous₂ hf).comp
      (continuous_id.div_const (2*Real.pi)))

 theorem sourceInverseKernel_memLp_two (f : ℝ → ℂ) (h1 : Integrable f)
    (h2 : MemLp f 2 volume) : MemLp (sourceInverseKernel f) 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm (sourceInverseKernel_continuous f h1).aestronglyMeasurable).mpr
  have hi := ((integrable_fourier_memLp_two f h1 h2).integrable_norm_pow
    (by norm_num : (2:ℕ) ≠ 0)).comp_div (by positivity : 2*Real.pi ≠ 0)
  simpa only [sourceInverseKernel, norm_smul, Real.norm_eq_abs, mul_pow] using
    hi.const_mul (|(2*Real.pi)⁻¹|^2)

 theorem sourceInverseKernel_plancherel (f : ℝ → ℂ) (h1 : Integrable f)
    (h2 : MemLp f 2 volume) :
    (∫ x, ‖sourceInverseKernel f x‖^2) = (2*Real.pi)⁻¹ * ∫ r, ‖f r‖^2 := by
  simp_rw [sourceInverseKernel, norm_smul, Real.norm_eq_abs, mul_pow]
  rw [integral_const_mul, Measure.integral_comp_div (fun x => ‖𝓕 f x‖^2),
    smul_eq_mul, abs_of_pos (by positivity : (0:ℝ)<2*Real.pi),
    abs_of_pos (by positivity : (0:ℝ)<(2*Real.pi)⁻¹),
    integrable_fourier_plancherel f h1 h2]
  field_simp

 theorem shellKernelMeasureConvolution_L2 (τ : Measure ℝ) [IsFiniteMeasure τ] (n : ℕ) :
    MemLp (kernelMeasureConvolution (sourceShellKernel n) τ) 2 volume ∧
    (∫ x, ‖kernelMeasureConvolution (sourceShellKernel n) τ x‖^2) ≤
      (2*Real.pi)⁻¹ * shellEnergy τ (n+1) := by
  have he : kernelMeasureConvolution (sourceShellKernel n) τ =
      sourceInverseKernel (sourceShellMultiplier τ n) := funext
    (shellKernelMeasureConvolution_fourier τ n)
  rw [he]
  have h1 : Integrable (sourceShellMultiplier τ n) :=
    memLp_one_iff_integrable.mp (sourceShellMultiplier_memLp τ n 1)
  have h2 := sourceShellMultiplier_memLp τ n 2
  refine ⟨sourceInverseKernel_memLp_two _ h1 h2, ?_⟩
  rw [sourceInverseKernel_plancherel _ h1 h2]
  exact mul_le_mul_of_nonneg_left (sourceShellMultiplier_energy_le τ n) (by positivity)

end PlanarFalconer

end OAI
