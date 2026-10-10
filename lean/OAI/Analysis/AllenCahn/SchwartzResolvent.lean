import Mathlib

namespace OAI

noncomputable section
namespace EllipticResolvent
open Filter Set Topology
open scoped NNReal
open scoped SchwartzMap Laplacian ContDiff
open FourierTransform
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def multiplier (x : E) : ℝ := (2+(2*Real.pi)^2*‖x‖^2)⁻¹

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma multiplier_temperate : (multiplier : E → ℝ).HasTemperateGrowth := by
  have hh : (fun x : E => (1+‖(Real.sqrt 2*Real.pi) • x‖^2)^(-1 : ℝ)).HasTemperateGrowth := by
    exact (Function.hasTemperateGrowth_one_add_norm_sq_rpow E (-1)).comp (by fun_prop)
  have he : (multiplier : E → ℝ) = fun x => (1/2 : ℝ)*(1+‖(Real.sqrt 2*Real.pi) • x‖^2)^(-1 : ℝ) := by
    funext x
    rw [Real.rpow_neg_one,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,mul_pow,
      Real.sq_sqrt (by norm_num)]
    dsimp [multiplier]
    field_simp
  rw [he]
  exact (Function.HasTemperateGrowth.const (1/2 : ℝ)).mul hh

lemma fourierMultiplier_add {a b : E → ℝ}
    (ha : a.HasTemperateGrowth) (hb : b.HasTemperateGrowth) :
    SchwartzMap.fourierMultiplierCLM ℂ (a+b) =
      SchwartzMap.fourierMultiplierCLM ℂ a+SchwartzMap.fourierMultiplierCLM ℂ b := by
  ext f
  simp [SchwartzMap.fourierMultiplierCLM_apply,SchwartzMap.smulLeftCLM_add ha hb]

lemma symbol_operator (f : 𝓢(E,ℂ)) :
    SchwartzMap.fourierMultiplierCLM ℂ (fun x : E => 2+(2*Real.pi)^2*‖x‖^2) f =
      (2 : ℝ) • f-Δ f := by
  have hd : (fun x : E => 2+(2*Real.pi)^2*‖x‖^2) =
      (fun _ : E => (2 : ℝ)) + ((2*Real.pi)^2 • fun x : E => ‖x‖^2) := rfl
  rw [hd,fourierMultiplier_add (by fun_prop) (by fun_prop),
    SchwartzMap.fourierMultiplierCLM_smul (by fun_prop),
    SchwartzMap.fourierMultiplierCLM_const,add_apply,
    SchwartzMap.laplacian_eq_fourierMultiplierCLM]
  simp

lemma inverse_operator (f : 𝓢(E,ℂ)) :
    let u := SchwartzMap.fourierMultiplierCLM ℂ (multiplier : E → ℝ) f
    (2 : ℝ) • u-Δ u=f := by
  dsimp only
  rw [← symbol_operator,SchwartzMap.fourierMultiplierCLM_fourierMultiplierCLM_apply
    (by fun_prop) multiplier_temperate]
  have he : ((fun x : E => 2+(2*Real.pi)^2*‖x‖^2) * multiplier) = fun _ => (1 : ℝ) := by
    funext x
    dsimp [multiplier]
    apply mul_inv_cancel₀
    positivity
  rw [he,SchwartzMap.fourierMultiplierCLM_const]
  simp

theorem exists_real_schwartz_resolvent (f : 𝓢(E,ℝ)) :
    ∃ u : 𝓢(E,ℝ), ∀ x, 2*u x-Laplacian.laplacian (u : E → ℝ) x=f x := by
  let fc : 𝓢(E,ℂ) := f.postcompCLM Complex.ofRealCLM
  let uc := SchwartzMap.fourierMultiplierCLM ℂ (multiplier : E → ℝ) fc
  let u : 𝓢(E,ℝ) := uc.postcompCLM Complex.reCLM
  refine ⟨u,fun x => ?_⟩
  have H := congrArg (fun v : 𝓢(E,ℂ) => (v x).re) (inverse_operator fc)
  have hL : Laplacian.laplacian (u : E → ℝ) x = (Laplacian.laplacian (uc : E → ℂ) x).re := by
    exact (uc.smooth 2).contDiffAt.laplacian_CLM_comp_left
  change 2*Complex.re (uc x)-Laplacian.laplacian (u : E → ℝ) x=f x
  rw [hL]
  simpa only [uc,sub_apply,smul_apply,Complex.sub_re,
    Complex.smul_re,smul_eq_mul,SchwartzMap.laplacian_apply,fc,SchwartzMap.postcompCLM_apply,
    Complex.ofRealCLM_apply,Complex.ofReal_re] using H

end EllipticResolvent
end

end OAI
