import Mathlib

namespace OAI

noncomputable section
namespace Ostmann.QuadraticSieve
open MeasureTheory Filter Complex
open scoped SchwartzMap FourierTransform Topology

def squarePullback (W : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : a ≠ 0) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLM ℂ (g := fun x : ℝ => a*x^2) (by fun_prop)
    (by
      refine ⟨1,1+|a|⁻¹,?_⟩
      intro x
      have hapos : 0 < |a| := abs_pos.mpr ha
      have hc : |a|⁻¹*|a|=1 := inv_mul_cancel₀ hapos.ne'
      simp only [Real.norm_eq_abs,abs_mul,abs_pow,pow_one]
      have hsq : |x|^2=x^2 := sq_abs x
      have hfirst : |x| ≤ 1+|x|^2 := by nlinarith [sq_nonneg (|x|-1)]
      have hsecond : 1+|x|^2 ≤ (1+|a|⁻¹)*(1+|a| *|x|^2) := by
        calc
          _ ≤ 1+|a|⁻¹+|a| *|x|^2+|x|^2 := by
            nlinarith [inv_nonneg.mpr hapos.le, mul_nonneg hapos.le (sq_nonneg |x|)]
          _ = 1+|a|⁻¹+|a| *|x|^2+(|a|⁻¹*|a|) *|x|^2 := by rw [hc]; ring
          _ = _ := by ring
      exact hfirst.trans hsecond) W

@[simp] theorem squarePullback_apply (W : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : a ≠ 0) (x : ℝ) :
    squarePullback W a ha x = W (a*x^2) := rfl

theorem integrable_squarePullback (W : 𝓢(ℝ, ℂ)) {a : ℝ} (ha : a ≠ 0) :
    Integrable (fun x : ℝ => W (a*x^2)) :=
  (squarePullback W a ha).integrable

def squareGaussianParameter (ε a t : ℝ) : ℂ :=
  (ε : ℂ)+(2*Real.pi*a*t : ℝ)*I

@[simp] theorem squareGaussianParameter_re (ε a t : ℝ) :
    (squareGaussianParameter ε a t).re=ε := by simp [squareGaussianParameter]

@[simp] theorem squareGaussianParameter_im (ε a t : ℝ) :
    (squareGaussianParameter ε a t).im=2*Real.pi*a*t := by simp [squareGaussianParameter]

def dampedSquareKernel (W : 𝓢(ℝ, ℂ)) (ε a x t : ℝ) : ℂ :=
  Complex.exp (-squareGaussianParameter ε a t*(x : ℂ)^2)*W t

theorem norm_dampedSquareKernel (W : 𝓢(ℝ, ℂ)) (ε a x t : ℝ) :
    ‖dampedSquareKernel W ε a x t‖=Real.exp (-ε*x^2)*‖W t‖ := by
  rw [dampedSquareKernel,norm_mul,norm_cexp_neg_mul_sq,squareGaussianParameter_re]

theorem integrable_dampedSquareKernel (W : 𝓢(ℝ, ℂ)) {ε : ℝ} (hε : 0<ε) (a : ℝ) :
    Integrable (Function.uncurry (dampedSquareKernel W ε a)) := by
  apply ((integrable_exp_neg_mul_sq hε).mul_prod W.integrable.norm).mono'
  · exact (by unfold dampedSquareKernel squareGaussianParameter Function.uncurry; fun_prop : Continuous (Function.uncurry (dampedSquareKernel W ε a))).aestronglyMeasurable
  · filter_upwards with z
    exact (norm_dampedSquareKernel W ε a z.1 z.2).le

theorem dampedSquareKernel_swap (W : 𝓢(ℝ, ℂ)) {ε : ℝ} (hε : 0<ε) (a : ℝ) :
    (∫ x : ℝ, ∫ t : ℝ, dampedSquareKernel W ε a x t) =
      ∫ t : ℝ, ((Real.pi : ℂ)/squareGaussianParameter ε a t)^(1/2 : ℂ)*W t := by
  rw [integral_integral_swap (integrable_dampedSquareKernel W hε a)]
  apply integral_congr_ae
  filter_upwards with t
  simp only [dampedSquareKernel]
  rw [integral_mul_const,integral_gaussian_complex]
  simpa using hε

end Ostmann.QuadraticSieve

end

end OAI
