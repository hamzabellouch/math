import OAI.NumberTheory.CubicMoment.Theta.CubicThetaLevelAngularCompleted
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

namespace OAI

/-! Entire continuation of the actual additive Dirichlet series in nonzero angular type.
Reciprocal Gamma factors remove the Mellin completion without adding an analytic input. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaAngularDirichletContinuation (q x y : Eisenstein) (rev : Bool) (k : ℕ) (s : ℂ) : ℂ :=
  4*(cubicThetaLevelScale q:ℂ)^(2*s+(k:ℂ)-1)*((2*Real.pi:ℝ):ℂ)^(2*s+(k:ℂ))*
    (Complex.Gamma (s+(k:ℂ)/2+1/6))⁻¹*(Complex.Gamma (s+(k:ℂ)/2-1/6))⁻¹*
    cubicThetaLevelAngularCompleted q x y rev k (2*s+(k:ℂ)-1)

theorem cubicThetaAngularDirichletContinuation_entire {q : Eisenstein} (hq : primary q)
    (x y : Eisenstein) (rev : Bool) (k : ℕ) :
    Differentiable ℂ (cubicThetaAngularDirichletContinuation q x y rev k) := by
  have hρ : (cubicThetaLevelScale q:ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (cubicThetaLevelScale_pos hq).ne'
  have hπ : ((2*Real.pi:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr (by positivity)
  have hA : Differentiable ℂ (fun s : ℂ => 2*s+(k:ℂ)-1) := by fun_prop
  have hB : Differentiable ℂ (fun s : ℂ => 2*s+(k:ℂ)) := by fun_prop
  have hC : Differentiable ℂ (fun s : ℂ => s+(k:ℂ)/2+1/6) := by fun_prop
  have hD : Differentiable ℂ (fun s : ℂ => s+(k:ℂ)/2-1/6) := by fun_prop
  exact (((((hA.const_cpow (Or.inl hρ)).const_mul 4).mul (hB.const_cpow (Or.inl hπ))).mul
    (Complex.differentiable_one_div_Gamma.comp hC)).mul
      (Complex.differentiable_one_div_Gamma.comp hD)).mul
        ((cubicThetaLevelAngularCompleted_entire hq x y rev k).comp hA)

theorem cubicThetaAngularDirichletContinuation_eq {q : Eisenstein} (hq : primary q)
    (x y : Eisenstein) (hxy : q∣9*x*y-1) (rev : Bool) {k : ℕ} (hk : 0<k)
    {s : ℂ} (hs : 3/2<s.re) :
    cubicThetaAngularDirichletContinuation q x y rev k s=
      cubicThetaDirichlet (fun n => theta (cubicThetaCircleOrder rev k) n*
        cubicThetaAdditiveCoefficient (-(3*(x:ℂ)/(q:ℂ))) n) (2*s-1) := by
  have h₁ : 0<(s+(k:ℂ)/2+1/6).re := by
    simp only [Complex.add_re,Complex.div_ofNat_re,Complex.natCast_re,Complex.one_re]
    have hkn : (0:ℝ)≤k := Nat.cast_nonneg k
    linarith
  have h₂ : 0<(s+(k:ℂ)/2-1/6).re := by
    simp only [Complex.add_re,Complex.sub_re,Complex.div_ofNat_re,Complex.natCast_re,Complex.one_re]
    have hkn : (0:ℝ)≤k := Nat.cast_nonneg k
    linarith
  have hG₁ := Complex.Gamma_ne_zero_of_re_pos h₁
  have hG₂ := Complex.Gamma_ne_zero_of_re_pos h₂
  have hρ : (cubicThetaLevelScale q:ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (cubicThetaLevelScale_pos hq).ne'
  have hπ : ((2*Real.pi:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr (by positivity)
  have hρp : (cubicThetaLevelScale q:ℂ)^(2*s+(k:ℂ)-1)≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hρ)
  have hπp : ((2*Real.pi:ℝ):ℂ)^(2*s+(k:ℂ))≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hπ)
  unfold cubicThetaAngularDirichletContinuation
  rw [cubicThetaLevelAngularCompleted_dirichlet hq x y hxy rev hk hs,
    show -2*(s+(k:ℂ)/2)=-(2*s+(k:ℂ)) by ring]
  rw [Complex.cpow_neg,Complex.cpow_neg]
  calc
    _ = ((cubicThetaLevelScale q:ℂ)^(2*s+(k:ℂ)-1)*
          ((cubicThetaLevelScale q:ℂ)^(2*s+(k:ℂ)-1))⁻¹)*
        (((2*Real.pi:ℝ):ℂ)^(2*s+(k:ℂ))*(((2*Real.pi:ℝ):ℂ)^(2*s+(k:ℂ)))⁻¹)*
        ((Complex.Gamma (s+(k:ℂ)/2+1/6))⁻¹*Complex.Gamma (s+(k:ℂ)/2+1/6))*
        ((Complex.Gamma (s+(k:ℂ)/2-1/6))⁻¹*Complex.Gamma (s+(k:ℂ)/2-1/6))*
          cubicThetaDirichlet (fun n => theta (cubicThetaCircleOrder rev k) n*
            cubicThetaAdditiveCoefficient (-(3*(x:ℂ)/(q:ℂ))) n) (2*s-1) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hρp,mul_inv_cancel₀ hπp,inv_mul_cancel₀ hG₁,inv_mul_cancel₀ hG₂]; simp

end CubicFirstMoment

end

end OAI
