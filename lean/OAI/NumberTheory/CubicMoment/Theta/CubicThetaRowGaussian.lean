import OAI.NumberTheory.CubicMoment.Estimates.GaussianSchwartz
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaEisensteinResidues

namespace OAI

/-! Shifted Gaussians for the actual Eisenstein row, with the exact
trace-Fourier scaling and translation factors. -/
noncomputable section
open scoped SchwartzMap
namespace CubicFirstMoment

def cubicThetaShiftedGaussian (c z : ℂ) (hc : c ≠ 0) (t : ℝ) (ht : 0 < t) :
    𝓢(ℂ,ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (complexMulEquiv c⁻¹ (inv_ne_zero hc))
    ((radialGaussianSchwartz t ht).compSubConstCLM ℂ (-z))

lemma cubicThetaShiftedGaussian_apply (c z : ℂ) (hc : c ≠ 0)
    (t : ℝ) (ht : 0 < t) (x : ℂ) :
    cubicThetaShiftedGaussian c z hc t ht x = (Real.exp (-t*‖z+x/c‖^2):ℂ) := by
  change radialGaussianSchwartz t ht (c⁻¹*x- -z) = _
  have he : c⁻¹*x- -z = z+x/c := by rw [div_eq_mul_inv]; ring
  rw [he, radialGaussianSchwartz_apply]

theorem cubicThetaShiftedGaussian_fourier (c z : ℂ) (hc : c ≠ 0)
    (t : ℝ) (ht : 0 < t) (w : ℂ) :
    traceFourier (cubicThetaShiftedGaussian c z hc t ht) w =
      (Complex.normSq c:ℂ)*(Real.fourierChar (tracePair z (w*c)):ℂ)*
        ((Real.pi/t:ℝ)*(Real.exp (-4*Real.pi^2/t*Complex.normSq (w*c)):ℝ)) := by
  have he : (cubicThetaShiftedGaussian c z hc t ht : ℂ → ℂ) =
      fun x => (fun u => radialGaussianSchwartz t ht (z+u)) (c⁻¹*x) := by
    funext x
    change radialGaussianSchwartz t ht (c⁻¹*x- -z) = _
    congr 1
    ring
  rw [he, traceFourier_complexMul c⁻¹ (inv_ne_zero hc)
    (fun u => radialGaussianSchwartz t ht (z+u)) w, Complex.normSq_inv, inv_inv,
    div_inv_eq_mul, traceFourier_translation, radialGaussianSchwartz_traceFourier]
  simp only [Complex.real_smul]
  ring

end CubicFirstMoment

end

end OAI
