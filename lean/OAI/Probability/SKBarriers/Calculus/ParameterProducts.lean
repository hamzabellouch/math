import Mathlib
import OAI.Probability.SKBarriers.Calculus.CubeDifferentiation

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
namespace SK.Analytic

theorem parameterDerivative_mul (n : ℕ) (f g : ParameterSpace n → ℝ)
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (z : ParameterSpace n) :
    parameterDerivative n (fun z => f z*g z) z =
      f z*parameterDerivative n g z + g z*parameterDerivative n f z := by
  have hh : HasFDerivAt (fun z => f z*g z)
      (f z • fderiv ℝ g z + g z • fderiv ℝ f z) z :=
    (hf z).hasFDerivAt.mul (hg z).hasFDerivAt
  rw [parameterDerivative, hh.fderiv]
  rfl

theorem parameterDerivative_exp_neg (n : ℕ) (V : ParameterSpace n → ℝ)
    (hV : Differentiable ℝ V) (z : ParameterSpace n) :
    parameterDerivative n (fun z => Real.exp (-V z)) z =
      -parameterDerivative n V z * Real.exp (-V z) := by
  have hh : HasFDerivAt (fun z => Real.exp (-V z))
      (Real.exp (-V z) • -fderiv ℝ V z) z := (hV z).hasFDerivAt.neg.exp
  rw [parameterDerivative, hh.fderiv]
  simp only [smul_apply, neg_apply, smul_eq_mul]
  dsimp only [parameterDerivative]
  ring

theorem parameterDerivative2_exp_neg (n : ℕ) (V : ParameterSpace n → ℝ)
    (hV : ContDiff ℝ 2 V) (z : ParameterSpace n) :
    parameterDerivative n (parameterDerivative n (fun z => Real.exp (-V z))) z =
      ((parameterDerivative n V z)^2 - parameterDerivative n (parameterDerivative n V) z) *
        Real.exp (-V z) := by
  have hvd := hV.differentiable (by norm_num)
  have hdv := (contDiff_parameterDerivative n V hV).differentiable (by norm_num)
  have he : parameterDerivative n (fun z => Real.exp (-V z)) =
      fun z => -parameterDerivative n V z * Real.exp (-V z) :=
    funext fun z => parameterDerivative_exp_neg n V hvd z
  have hneg : Differentiable ℝ (fun z => -parameterDerivative n V z) := hdv.neg
  rw [he, parameterDerivative_mul n _ _ hneg (hV.neg.exp.differentiable (by norm_num))]
  rw [parameterDerivative_exp_neg n V hvd z]
  have hn : parameterDerivative n (fun z => -parameterDerivative n V z) z =
      -parameterDerivative n (parameterDerivative n V) z := by
    have hh : HasFDerivAt (fun z => -parameterDerivative n V z)
        (-fderiv ℝ (parameterDerivative n V) z) z := (hdv z).hasFDerivAt.neg
    rw [parameterDerivative, hh.fderiv]
    rfl
  rw [hn]
  ring

def tiltedPotential (n : ℕ) (V : ParameterSpace n → ℝ) (L : ParameterSpace n →L[ℝ] ℝ)
    (K : ℝ) (z : ParameterSpace n) : ℝ :=
  V z - parameter n z * L z + (K/2)*(parameter n z*parameter n z)

theorem contDiff_tiltedPotential (n : ℕ) (V : ParameterSpace n → ℝ)
    (hV : ContDiff ℝ 2 V) (L : ParameterSpace n →L[ℝ] ℝ) (K : ℝ) :
    ContDiff ℝ 2 (tiltedPotential n V L K) :=
  (hV.sub ((parameter n).contDiff.mul L.contDiff)).add
    (contDiff_const.mul ((parameter n).contDiff.mul (parameter n).contDiff))

theorem parameterDerivative_tiltedPotential (n : ℕ) (V : ParameterSpace n → ℝ)
    (hV : Differentiable ℝ V) (hV₀ : ∀ z, parameterDerivative n V z = 0)
    (L : ParameterSpace n →L[ℝ] ℝ) (hL : L (parameterAxis n) = 0) (K : ℝ)
    (z : ParameterSpace n) :
    parameterDerivative n (tiltedPotential n V L K) z = K*parameter n z-L z := by
  let p := parameter n
  have hh : HasFDerivAt (tiltedPotential n V L K)
      (fderiv ℝ V z-(p z • L+L z • p)+(K/2) • (p z • p+p z • p)) z :=
    ((hV z).hasFDerivAt.sub (p.hasFDerivAt.mul L.hasFDerivAt)).add
      ((p.hasFDerivAt.mul p.hasFDerivAt).const_mul (K/2))
  rw [parameterDerivative, hh.fderiv]
  simp only [add_apply, sub_apply, smul_apply, smul_eq_mul,
    show p (parameterAxis n) = 1 from parameter_axis n, hL, mul_zero, mul_one]
  have hz := hV₀ z
  dsimp only [parameterDerivative] at hz
  rw [hz]
  dsimp only [p]
  ring

theorem parameterDerivative2_tiltedPotential (n : ℕ) (V : ParameterSpace n → ℝ)
    (hV : Differentiable ℝ V) (hV₀ : ∀ z, parameterDerivative n V z = 0)
    (L : ParameterSpace n →L[ℝ] ℝ) (hL : L (parameterAxis n) = 0) (K : ℝ)
    (z : ParameterSpace n) :
    parameterDerivative n (parameterDerivative n (tiltedPotential n V L K)) z = K := by
  have he : parameterDerivative n (tiltedPotential n V L K) = fun z => K*parameter n z-L z :=
    funext fun z => parameterDerivative_tiltedPotential n V hV hV₀ L hL K z
  rw [he]
  have hh : HasFDerivAt (fun z => K*parameter n z-L z) (K • parameter n - L) z :=
    ((parameter n).hasFDerivAt.const_mul K).sub L.hasFDerivAt
  rw [parameterDerivative, hh.fderiv]
  simp only [sub_apply, smul_apply, smul_eq_mul, parameter_axis, hL,
    mul_one, sub_zero]

end SK.Analytic

end
end
end
end
end

end OAI
