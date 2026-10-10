import OAI.NumberTheory.CubicMoment.Theta.CubicThetaScalarGaussianError

namespace OAI

/-! Real positive form of the scalar lattice Gaussian and its uniform bound. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaScalarGaussianReal (z : ℂ) (t : ℝ) : ℝ :=
  ∑' a : Eisenstein,Real.exp (-t*Complex.normSq (z+3*(a:ℂ)))

lemma cubicThetaScalarGaussianReal_cast (z : ℂ) (t : ℝ) :
    (cubicThetaScalarGaussianReal z t:ℂ)=cubicThetaScalarGaussian z t := by
  exact Complex.ofReal_tsum _

lemma cubicThetaScalarGaussianReal_summable (z : ℂ) {t : ℝ} (ht : 0<t) :
    Summable (fun a : Eisenstein => Real.exp (-t*Complex.normSq (z+3*(a:ℂ)))) := by
  convert (cubicThetaScalarGaussian_summable z ht).norm using 1
  ext a
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]

lemma cubicThetaScalarGaussianReal_nonneg (z : ℂ) (t : ℝ) :
    0≤cubicThetaScalarGaussianReal z t := tsum_nonneg (fun _ => (Real.exp_pos _).le)

lemma cubicThetaScalarGaussianReal_error (z : ℂ) {t : ℝ} (ht : 0<t) :
    |cubicThetaScalarGaussianReal z t-2*Real.pi/(9*Real.sqrt 3*t)|≤
      (2*Real.pi/(9*Real.sqrt 3*t))*cubicThetaLatticeGaussianTail (4*Real.pi^2/(27*t)) := by
  have h := cubicThetaScalarGaussian_error z ht
  rw [←cubicThetaScalarGaussianReal_cast,←Complex.ofReal_sub,Complex.norm_real,
    Real.norm_eq_abs] at h
  exact h

lemma cubicThetaScalarGaussianReal_le (z : ℂ) {t : ℝ} (ht : 0<t) :
    cubicThetaScalarGaussianReal z t≤(2*Real.pi/(9*Real.sqrt 3*t))*
      (1+cubicThetaLatticeGaussianTail (4*Real.pi^2/(27*t))) := by
  have h := (le_abs_self _).trans (cubicThetaScalarGaussianReal_error z ht)
  linarith

lemma cubicThetaScalarGaussianReal_zero_summand (a : Eisenstein) (t : ℝ) :
    Real.exp (-t*Complex.normSq (0+3*(a:ℂ)))=Real.exp (-9*t*norm a) := by
  rw [zero_add,Complex.normSq_mul,show Complex.normSq (3:ℂ)=9 by
    norm_num [Complex.normSq_apply]]
  congr 1
  change -t*(9*norm a)=_
  ring

end CubicFirstMoment

end

end OAI
