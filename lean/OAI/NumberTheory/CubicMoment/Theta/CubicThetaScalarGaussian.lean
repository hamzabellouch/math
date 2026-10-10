import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRowGaussian
import OAI.NumberTheory.CubicMoment.Estimates.PrincipalIdealTheta

namespace OAI

/-! The unweighted Gaussian on the affine level-three lattice. This is the
scalar Poisson kernel used to compute the height-series residue. -/
noncomputable section
open scoped SchwartzMap
namespace CubicFirstMoment

def cubicThetaScalarGaussian (z : ℂ) (t : ℝ) : ℂ :=
  ∑' a : Eisenstein,(Real.exp (-t*Complex.normSq (z+3*(a:ℂ))):ℂ)

lemma cubicThetaScalarGaussian_summable (z : ℂ) {t : ℝ} (ht : 0<t) :
    Summable (fun a : Eisenstein =>
      (Real.exp (-t*Complex.normSq (z+3*(a:ℂ))):ℂ)) := by
  let F := cubicThetaShiftedGaussian (1/3) z (by norm_num) t ht
  have h := schwartz_summable_eisenstein F
  convert h using 1
  funext a
  dsimp only [F]
  rw [cubicThetaShiftedGaussian_apply,Complex.normSq_eq_norm_sq]
  rw [show (a:ℂ)/(1/3)=3*(a:ℂ) by ring]

theorem cubicThetaScalarGaussian_poisson (z : ℂ) {t : ℝ} (ht : 0<t) :
    cubicThetaScalarGaussian z t=(2*Real.pi/(9*Real.sqrt 3*t):ℝ)*
      ∑' h : Eisenstein,
        (Real.fourierChar (tracePair z ((h:ℂ)/(3*traceLambda))):ℂ)*
          (Real.exp (-(4*Real.pi^2/(27*t))*norm h):ℂ) := by
  have hp := poisson_eisenstein_coset (radialGaussianSchwartz t ht)
    (3:ℂ) (by norm_num) z
  simp_rw [radialGaussianSchwartz_apply,radialGaussianSchwartz_traceFourier] at hp
  have he (h : Eisenstein) :
      -4*Real.pi^2/t*Complex.normSq ((h:ℂ)/(3*traceLambda))=
        -(4*Real.pi^2/(27*t))*norm h := by
    rw [Complex.normSq_div,Complex.normSq_mul,traceLambda_normSq]
    rw [show Complex.normSq (3:ℂ)=9 by norm_num [Complex.normSq_apply]]
    change -4*Real.pi^2/t*(norm h/(9*3))=_
    ring
  simp_rw [he] at hp
  rw [show Complex.normSq (3:ℂ)=9 by norm_num [Complex.normSq_apply]] at hp
  simp only [Complex.real_smul] at hp
  rw [show cubicThetaScalarGaussian z t=
      ∑' a : Eisenstein,(Real.exp (-t*‖z+3*(a:ℂ)‖^2):ℂ) by
    simp only [cubicThetaScalarGaussian,Complex.normSq_eq_norm_sq]]
  rw [hp]
  simp_rw [show ∀ h : Eisenstein,
    (Real.fourierChar (tracePair z ((h:ℂ)/(3*traceLambda))):ℂ)*
      ((Real.pi/t:ℝ)*(Real.exp (-(4*Real.pi^2/(27*t))*norm h):ℂ))=
    (Real.pi/t:ℝ)*((Real.fourierChar (tracePair z ((h:ℂ)/(3*traceLambda))):ℂ)*
      (Real.exp (-(4*Real.pi^2/(27*t))*norm h):ℂ)) from fun _ => by ring]
  rw [tsum_mul_left,←mul_assoc]
  congr 1
  push_cast
  ring

end CubicFirstMoment

end

end OAI
