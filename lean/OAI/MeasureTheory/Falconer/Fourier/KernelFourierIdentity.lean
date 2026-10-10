import OAI.MeasureTheory.Falconer.Fourier.MeasureKernelConvolution
import OAI.MeasureTheory.Falconer.Shells.ShellFrequencyEnergy

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set Filter

theorem sourceInverseKernel_measure (f : ℝ → ℂ) (hf : Continuous f) (hi : Integrable f)
    (τ : Measure ℝ) [IsFiniteMeasure τ] (x : ℝ) :
    kernelMeasureConvolution (sourceInverseKernel f) τ x =
      sourceInverseKernel (fun r => f r * charFun τ r) x := by
  let g : ℝ × ℝ → ℂ := fun z =>
    Complex.exp (↑(-x*z.1)*Complex.I) * f z.1 * Complex.exp (↑(z.1*z.2)*Complex.I)
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hb : Integrable (fun z : ℝ × ℝ => ‖f z.1‖ * (1:ℝ)) (volume.prod τ) :=
    hi.norm.mul_prod (integrable_const 1)
  have hp : Integrable g (volume.prod τ) := hb.mono' hg.aestronglyMeasurable (by
    filter_upwards with z
    simp [g, Complex.norm_exp, Complex.mul_re])
  have he (r y : ℝ) : Complex.exp (↑(-(x-y)*r)*Complex.I) * f r = g (r,y) := by
    have ha : (↑(-(x-y)*r) : ℂ)*Complex.I =
        ↑(-x*r)*Complex.I + ↑(r*y)*Complex.I := by push_cast; ring
    rw [ha, Complex.exp_add]
    dsimp [g]
    ring
  unfold kernelMeasureConvolution
  simp_rw [sourceInverseKernel_formula, he]
  rw [integral_smul, ← integral_integral_swap hp]
  congr 1
  apply integral_congr_ae
  filter_upwards with r
  dsimp [g]
  rw [integral_const_mul, charFun_apply_real]
  simp only [Complex.ofReal_mul]
  rw [mul_assoc]

theorem shellKernelMeasureConvolution_fourier (τ : Measure ℝ) [IsFiniteMeasure τ]
    (n : ℕ) (x : ℝ) :
    kernelMeasureConvolution (sourceShellKernel n) τ x =
      sourceInverseKernel (sourceShellMultiplier τ n) x := by
  exact sourceInverseKernel_measure (sourceShellSchwartz n)
    (sourceShellSchwartz n).continuous (sourceShellSchwartz n).integrable τ x

end PlanarFalconer

end OAI
