import OAI.NumberTheory.CubicMoment.Theta.CubicThetaLogHeight
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRowGaussBounds
import Mathlib.Analysis.Fourier.FourierTransformDeriv

namespace OAI

/-! Separation of the actual trace-Fourier modes of the Eisenstein series.
The logarithmic radial operator has potential 16*pi^2*|w|^2*exp(2t). -/
noncomputable section
namespace CubicFirstMoment

lemma cubicTheta_affineCharacter_hasDerivAt (a b x : ℝ) :
    HasDerivAt (fun t : ℝ => (Real.fourierChar (a*t+b):ℂ))
      ((2*Real.pi*Complex.I*(a:ℂ))*(Real.fourierChar (a*x+b):ℂ)) x := by
  have h := (Real.hasDerivAt_fourierChar (a*x+b)).scomp x
    (((hasDerivAt_id x).const_mul a).add_const b)
  convert h using 1
  · rfl
  · simp only [mul_one,Complex.real_smul]
    ring

lemma cubicTheta_affineCharacter_second (a b x : ℝ) :
    deriv (deriv (fun t : ℝ => (Real.fourierChar (a*t+b):ℂ))) x=
      (2*Real.pi*Complex.I*(a:ℂ))^2*(Real.fourierChar (a*x+b):ℂ) := by
  have he : deriv (fun t : ℝ => (Real.fourierChar (a*t+b):ℂ))=
      (fun t => (2*Real.pi*Complex.I*(a:ℂ))*(Real.fourierChar (a*t+b):ℂ)) :=
    funext (fun t => (cubicTheta_affineCharacter_hasDerivAt a b t).deriv)
  rw [he]
  rw [((cubicTheta_affineCharacter_hasDerivAt a b x).const_mul (2*Real.pi*Complex.I*(a:ℂ))).deriv]
  ring

def cubicThetaFourierPhase (w : ℂ) (x y : ℝ) : ℂ :=
  Real.fourierChar (2*(x*w.re-y*w.im))

lemma cubicThetaFourierPhase_eq (w : ℂ) (x y : ℝ) :
    cubicThetaFourierPhase w x y=
      (Real.fourierChar (tracePair ((x:ℂ)+(y:ℂ)*Complex.I) w):ℂ) := by
  simp [cubicThetaFourierPhase, tracePair, Complex.mul_re]

lemma cubicThetaFourierPhase_second_x (w : ℂ) (x y : ℝ) :
    deriv (deriv (fun t => cubicThetaFourierPhase w t y)) x=
      (4*Real.pi*Complex.I*(w.re:ℂ))^2*cubicThetaFourierPhase w x y := by
  have he : (fun t => cubicThetaFourierPhase w t y)=
      (fun t : ℝ => (Real.fourierChar ((2*w.re)*t+(-2*y*w.im)):ℂ)) := by
    funext t
    unfold cubicThetaFourierPhase
    congr 2
    ring
  rw [he,cubicTheta_affineCharacter_second]
  unfold cubicThetaFourierPhase
  have ha : (2*w.re)*x+(-2*y*w.im)=2*(x*w.re-y*w.im) := by ring
  rw [ha]
  push_cast
  ring

lemma cubicThetaFourierPhase_second_y (w : ℂ) (x y : ℝ) :
    deriv (deriv (fun t => cubicThetaFourierPhase w x t)) y=
      (-4*Real.pi*Complex.I*(w.im:ℂ))^2*cubicThetaFourierPhase w x y := by
  have he : (fun t => cubicThetaFourierPhase w x t)=
      (fun t : ℝ => (Real.fourierChar ((-2*w.im)*t+2*x*w.re):ℂ)) := by
    funext t
    unfold cubicThetaFourierPhase
    congr 2
    ring
  rw [he,cubicTheta_affineCharacter_second]
  unfold cubicThetaFourierPhase
  have ha : (-2*w.im)*y+2*x*w.re=2*(x*w.re-y*w.im) := by ring
  rw [ha]
  push_cast
  ring

lemma cubicThetaFourierPhase_laplacian (w : ℂ) (x y : ℝ) :
    deriv (deriv (fun t => cubicThetaFourierPhase w t y)) x+
      deriv (deriv (fun t => cubicThetaFourierPhase w x t)) y=
      -(16*Real.pi^2*Complex.normSq w:ℝ)*cubicThetaFourierPhase w x y := by
  rw [cubicThetaFourierPhase_second_x,cubicThetaFourierPhase_second_y]
  simp only [Complex.normSq_apply]
  push_cast
  ring_nf
  simp only [Complex.I_sq]
  ring

end CubicFirstMoment

end

end OAI
