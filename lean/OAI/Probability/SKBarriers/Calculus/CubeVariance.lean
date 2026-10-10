import Mathlib
import OAI.Probability.SKBarriers.Calculus.HessianAlgebra
import OAI.Probability.SKBarriers.Calculus.ParameterProducts

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

theorem cube_linear_variance_le_aux (n : ℕ) (V : ParameterSpace n → ℝ)
    (hV : ContDiff ℝ 2 V) (hV₀ : ∀ z, parameterDerivative n V z = 0)
    (L : ParameterSpace n →L[ℝ] ℝ) (hL₀ : L (parameterAxis n) = 0)
    {c ε A : ℝ} (hε : 0 < ε) (hεc : ε < c) (hA : 0 ≤ A)
    (hL : ∀ u, (L u)^2 ≤ A*coordinateSquare n u)
    (hH : ∀ z u, c*coordinateSquare n u ≤ Hessian V z u u)
    {a b : ℝ} (hab : a < b) :
    let w := fun z => Real.exp (-V z)
    let Z := cubeIntegral n w a b 0
    cubeIntegral n (fun z => (L z)^2*w z) a b 0/Z -
      (cubeIntegral n (fun z => L z*w z) a b 0/Z)^2 ≤ A/(c-ε) := by
  let K := A/(c-ε)
  let T := tiltedPotential n V L K
  let w : ParameterSpace n → ℝ := fun z => Real.exp (-V z)
  let W : ParameterSpace n → ℝ := fun z => Real.exp (-T z)
  let Z := cubeIntegral n w a b 0
  let I₁ := cubeIntegral n (fun z => L z*w z) a b 0
  let I₂ := cubeIntegral n (fun z => (L z)^2*w z) a b 0
  have hT : ContDiff ℝ 2 T := contDiff_tiltedPotential n V hV L K
  have hessianT (z u : ParameterSpace n) : ε*coordinateSquare n u ≤ Hessian T z u u := by
    exact hessian_tilt_lower hV (parameter n) L (coordinateSquare n) hεc hA
      (coordinateSquare_nonneg n) hL hH z u
  have hpos := (cubePotential_hessian_lower n T hT hε hessianT hab).2 0 1
  have hformula := cubePotential_hessian_formula n T hT hab 0
  have hW (z : ParameterSpace n) (hz : parameter n z = 0) : W z = w z := by
    simp only [W, T, tiltedPotential, hz, zero_mul, sub_zero, mul_zero, add_zero, w]
  have hZ : 0 < Z := cubeIntegral_pos n w hV.neg.exp.continuous
    (fun _ => Real.exp_pos _) hab 0
  have hZeq : cubeIntegral n W a b 0 = Z :=
    cubeIntegral_congr_parameter n W w a b 0 hW
  have hZ₁eq : cubeIntegral n (parameterDerivative n W) a b 0 = I₁ := by
    apply cubeIntegral_congr_parameter
    intro z hz
    rw [parameterDerivative_exp_neg n T (hT.differentiable (by norm_num)),
      parameterDerivative_tiltedPotential n V (hV.differentiable (by norm_num)) hV₀ L hL₀]
    change -(K*parameter n z-L z)*W z = L z*w z
    rw [hz, mul_zero, zero_sub, neg_neg, hW z hz]
  have hZ₂eq : cubeIntegral n (parameterDerivative n (parameterDerivative n W)) a b 0 = I₂-K*Z := by
    have he := cubeIntegral_congr_parameter n
      (parameterDerivative n (parameterDerivative n W))
      (fun z => (L z)^2*w z-K*w z) a b 0 (by
        intro z hz
        rw [parameterDerivative2_exp_neg n T hT,
          parameterDerivative_tiltedPotential n V (hV.differentiable (by norm_num)) hV₀ L hL₀,
          parameterDerivative2_tiltedPotential n V (hV.differentiable (by norm_num)) hV₀ L hL₀]
        change ((K*parameter n z-L z)^2-K)*W z = _
        rw [hz, hW z hz]
        ring)
    have hcF : Continuous (fun z => (L z)^2*w z) := (L.continuous.pow 2).mul hV.neg.exp.continuous
    have hcG : Continuous (fun z => K*w z) := hV.neg.exp.continuous.const_mul K
    rw [he, cubeIntegral_sub n _ _ hcF hcG, cubeIntegral_const_mul]
  change Hessian (cubePotential n T a b) 0 1 1 =
    (cubeIntegral n (parameterDerivative n W) a b 0/cubeIntegral n W a b 0)^2 -
      cubeIntegral n (parameterDerivative n (parameterDerivative n W)) a b 0/cubeIntegral n W a b 0
    at hformula
  rw [hZeq, hZ₁eq, hZ₂eq] at hformula
  change I₂/Z-(I₁/Z)^2 ≤ K
  have he : (I₁/Z)^2-(I₂-K*Z)/Z = K-(I₂/Z-(I₁/Z)^2) := by
    field_simp
    ring
  rw [he] at hformula
  linarith

theorem cube_linear_variance_le (n : ℕ) (V : ParameterSpace n → ℝ)
    (hV : ContDiff ℝ 2 V) (hV₀ : ∀ z, parameterDerivative n V z = 0)
    (L : ParameterSpace n →L[ℝ] ℝ) (hL₀ : L (parameterAxis n) = 0)
    {c A : ℝ} (hc : 0 < c) (hA : 0 ≤ A)
    (hL : ∀ u, (L u)^2 ≤ A*coordinateSquare n u)
    (hH : ∀ z u, c*coordinateSquare n u ≤ Hessian V z u u)
    {a b : ℝ} (hab : a < b) :
    let w := fun z => Real.exp (-V z)
    let Z := cubeIntegral n w a b 0
    cubeIntegral n (fun z => (L z)^2*w z) a b 0/Z -
      (cubeIntegral n (fun z => L z*w z) a b 0/Z)^2 ≤ A/c := by
  let w : ParameterSpace n → ℝ := fun z => Real.exp (-V z)
  let Z := cubeIntegral n w a b 0
  let v := cubeIntegral n (fun z => (L z)^2*w z) a b 0/Z -
    (cubeIntegral n (fun z => L z*w z) a b 0/Z)^2
  change v ≤ A/c
  by_contra hh
  have hv : A/c < v := lt_of_not_ge hh
  have hvpos := lt_of_le_of_lt (div_nonneg hA hc.le) hv
  have hAv : A < v*c := (div_lt_iff₀ hc).mp hv
  have hAc : A/v < c := (div_lt_iff₀ hvpos).mpr (by nlinarith)
  let ε := (c-A/v)/2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hεc : ε < c := by dsimp [ε]; have := div_nonneg hA hvpos.le; linarith
  have hbound := cube_linear_variance_le_aux n V hV hV₀ L hL₀ hε hεc hA hL hH hab
  change v ≤ A/(c-ε) at hbound
  have hstrict : A/(c-ε) < v := by
    apply (div_lt_iff₀ (sub_pos.mpr hεc)).mpr
    have he : A/v*v = A := div_mul_cancel₀ A (ne_of_gt hvpos)
    dsimp only [ε]
    nlinarith
  exact (lt_irrefl v) (hbound.trans_lt hstrict)

end SK.Analytic

end
end
end
end
end

end OAI
