import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFourierMode
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialEnergy

namespace OAI

/-! The exact separated radial operator for the trace-Fourier lattice.
This retains the factor four between the heat scale and the Laplacian potential. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaHyperbolicOperator_fourier (w : ℂ) (f : ℝ → ℂ) (x y v : ℝ) :
    cubicThetaHyperbolicOperator (fun a b t => cubicThetaFourierPhase w a b*f t) x y v=
      cubicThetaFourierPhase w x y*
        (cubicThetaHyperbolicOperator (fun _ _ t => f t) x y v-
          (v:ℂ)^2*(16*Real.pi^2*Complex.normSq w:ℝ)*f v) := by
  unfold cubicThetaHyperbolicOperator
  simp only [deriv_mul_const_field',deriv_const_mul_field',deriv_const',deriv_const,zero_add]
  calc
    _ = (v:ℂ)^2*((deriv (deriv (fun t => cubicThetaFourierPhase w t y)) x+
        deriv (deriv (fun t => cubicThetaFourierPhase w x t)) y)*f v+
        cubicThetaFourierPhase w x y*deriv (deriv f) v)-
          (v:ℂ)*(cubicThetaFourierPhase w x y*deriv f v) := by ring
    _ = _ := by rw [cubicThetaFourierPhase_laplacian]; push_cast; ring

def cubicThetaFourierLogLift (w : ℂ) (f : ℝ → ℂ) (x y v : ℝ) : ℂ :=
  cubicThetaFourierPhase w x y*cubicThetaLogLift f v

theorem cubicThetaFourierLogLift_equation (w : ℂ) {f : ℝ → ℂ}
    (hf : Differentiable ℝ f) (hf' : Differentiable ℝ (deriv f))
    (x y : ℝ) {v : ℝ} (hv : 0<v) :
    cubicThetaHyperbolicOperator (cubicThetaFourierLogLift w f) x y v=
      -cubicThetaFourierPhase w x y*(v:ℂ)*
        cubicThetaRadialOperator (16*Real.pi^2*Complex.normSq w) f (Real.log v) := by
  unfold cubicThetaFourierLogLift
  rw [cubicThetaHyperbolicOperator_fourier,
    cubicThetaHyperbolicOperator_logLift hf hf' x y hv]
  have he : Real.exp (2*Real.log v)=v^2 := by
    rw [two_mul,Real.exp_add,Real.exp_log hv]
    ring
  unfold cubicThetaRadialOperator cubicThetaLogLift
  rw [he]
  simp only [Complex.real_smul]
  push_cast
  ring

lemma cubicThetaFourierRadial_scale (h : Eisenstein) :
    16*Real.pi^2*Complex.normSq (cubicThetaRowFrequency h)=4*cubicThetaRowHeatScale h := by
  unfold cubicThetaRowHeatScale
  ring

theorem cubicThetaFourierLogLift_lattice_equation (h : Eisenstein) {f : ℝ → ℂ}
    (hf : Differentiable ℝ f) (hf' : Differentiable ℝ (deriv f))
    (x y : ℝ) {v : ℝ} (hv : 0<v) :
    cubicThetaHyperbolicOperator (cubicThetaFourierLogLift (cubicThetaRowFrequency h) f) x y v=
      -cubicThetaFourierPhase (cubicThetaRowFrequency h) x y*(v:ℂ)*
        cubicThetaRadialOperator (4*cubicThetaRowHeatScale h) f (Real.log v) := by
  rw [cubicThetaFourierLogLift_equation (cubicThetaRowFrequency h) hf hf' x y hv,
    cubicThetaFourierRadial_scale]

end CubicFirstMoment

end

end OAI
