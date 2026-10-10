import OAI.MeasureTheory.Falconer.Estimates.SpatialPlancherel
import OAI.MeasureTheory.Falconer.Shells.ShellFrequencyTests

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set Filter
open scoped FourierTransform SchwartzMap Topology

 theorem sourceInverseKernel_pairing (f : ℝ → ℂ) (hf : Integrable f)
    (φ : 𝓢(ℝ, ℂ)) :
    (∫ x, φ x * sourceInverseKernel f x) =
      (2*Real.pi)⁻¹ • ∫ r, f r * 𝓕 φ (r/(2*Real.pi)) := by
  let g : ℝ × ℝ → ℂ := fun z =>
    φ z.1 * (Complex.exp (↑(-z.1*z.2)*Complex.I) * f z.2)
  have hg : AEStronglyMeasurable g (volume.prod volume) :=
    φ.continuous.aestronglyMeasurable.comp_fst.mul
      ((by fun_prop : Continuous (fun z : ℝ × ℝ =>
        Complex.exp (↑(-z.1*z.2)*Complex.I))).aestronglyMeasurable.mul
        hf.aestronglyMeasurable.comp_snd)
  have hi : Integrable g (volume.prod volume) :=
    (φ.integrable.norm.mul_prod hf.norm).mono' hg (by
      filter_upwards with z
      simp [g, Complex.norm_exp, Complex.mul_re])
  simp_rw [sourceInverseKernel_formula, mul_smul_comm, ← integral_const_mul]
  rw [integral_smul, integral_integral_swap hi]
  congr 1
  apply integral_congr_ae
  filter_upwards with r
  rw [SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  have he : -2*Real.pi*x*(r/(2*Real.pi)) = -x*r := by field_simp
  rw [he, smul_eq_mul]
  ring

 theorem sourceSchwartz_inversion (φ : 𝓢(ℝ, ℂ)) (y : ℝ) :
    (2*Real.pi)⁻¹ • (∫ r, Complex.exp (↑(r*y)*Complex.I) * 𝓕 φ (r/(2*Real.pi))) = φ y := by
  have hs := Measure.integral_comp_div
    (fun u : ℝ => Complex.exp (↑(2*Real.pi*u*y)*Complex.I) * 𝓕 φ u) (2*Real.pi)
  have he (r : ℝ) : 2*Real.pi*(r/(2*Real.pi))*y = r*y := by field_simp
  simp_rw [he] at hs
  rw [hs, abs_of_pos (by positivity : (0:ℝ)<2*Real.pi), smul_smul,
    inv_mul_cancel₀ (by positivity), one_smul]
  have h := congrArg (fun ψ : 𝓢(ℝ, ℂ) => ψ y)
    (show (𝓕⁻ (𝓕 φ : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ)) = φ from
      FourierTransform.fourierInv_fourier_eq φ)
  simpa only [SchwartzMap.fourierInv_coe, Real.fourierInv_eq', real_inner_eq_re_inner,
    RCLike.inner_apply, conj_trivial, smul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using h

 theorem source_characteristic_schwartz_test (τ : Measure ℝ) [IsFiniteMeasure τ]
    (φ : 𝓢(ℝ, ℂ)) :
    (2*Real.pi)⁻¹ • (∫ r, charFun τ r * 𝓕 φ (r/(2*Real.pi))) = ∫ y, φ y ∂τ := by
  let f : ℝ → ℂ := fun r => 𝓕 φ (r/(2*Real.pi))
  have hf : Integrable f := (𝓕 φ).integrable.comp_div (by positivity)
  let g : ℝ × ℝ → ℂ := fun z => Complex.exp (↑(z.1*z.2)*Complex.I)*f z.1
  have hp : Integrable g (volume.prod τ) :=
    (hf.norm.comp_fst τ).mono' (by dsimp [g, f]; fun_prop) (by
      filter_upwards with z
      simp [g, Complex.norm_exp, Complex.mul_re])
  simp_rw [charFun_apply_real, ← integral_mul_const]
  have he (r y : ℝ) : Complex.exp ((r:ℂ)*(y:ℂ)*Complex.I) * f r = g (r,y) := by
    simp [g, Complex.ofReal_mul]
  change (2*Real.pi)⁻¹ • (∫ r : ℝ, ∫ y : ℝ, Complex.exp ((r:ℂ)*(y:ℂ)*Complex.I) * f r ∂τ) = _
  simp_rw [he]
  rw [integral_integral_swap hp, ← integral_smul]
  apply integral_congr_ae
  filter_upwards with y
  exact sourceSchwartz_inversion φ y

end PlanarFalconer

end OAI
