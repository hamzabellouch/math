import OAI.NumberTheory.CubicMoment.Theta.CubicThetaMassEuler
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaConstantModeResidue

namespace OAI

/-! The exact residue of the arithmetic coefficient-energy Dirichlet series.
This is an arithmetic calculation, before comparison with the global norm. -/
noncomputable section
open Filter
open scoped Topology
namespace CubicFirstMoment

def cubicThetaMassRegular (s : ℂ) : ℂ :=
  cubicThetaMassEulerPrefactor s * principalZetaRegularFactor (1+s) *
    principalIdealZeta (2+3*s) / principalIdealZeta (2+2*s)

lemma cubicThetaMassEulerPrefactor_analyticAt_zero :
    AnalyticAt ℂ cubicThetaMassEulerPrefactor 0 := by
  let _ : NeZero (3:ℂ) := ⟨by norm_num⟩
  have hp (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) :
      AnalyticAt ℂ (fun s => (3:ℂ)^(f s)) 0 :=
    ((differentiable_const_cpow_of_neZero (3:ℂ)).analyticAt _).comp hf
  have hq := hp (fun s => -2-3*s) (by fun_prop)
  have h1 := hp (fun s => -(1+s)) (by fun_prop)
  have h2 := hp (fun s => -(2+3*s)) (by fun_prop)
  have h3 := hp (fun s => -(2+2*s)) (by fun_prop)
  have h8 := hp (fun s => 8-s) (by fun_prop)
  have hn : 1-(3:ℂ)^(-2-3*(0:ℂ))≠0 := by norm_num [Complex.cpow_neg,Complex.cpow_ofNat]
  have hd : 1-(3:ℂ)^(-(2+2*(0:ℂ)))≠0 := by norm_num [Complex.cpow_neg,Complex.cpow_ofNat]
  have hi := (analyticAt_const.sub hq).inv hn
  unfold cubicThetaMassEulerPrefactor
  exact ((((analyticAt_const.mul (hi.sub analyticAt_const)).add
    ((analyticAt_const.mul h8).mul hi)).mul (analyticAt_const.sub h1)).mul
      (analyticAt_const.sub h2)).div (analyticAt_const.sub h3) hd

lemma cubicThetaMassRegular_analyticAt_zero : AnalyticAt ℂ cubicThetaMassRegular 0 := by
  have hr : AnalyticAt ℂ (fun s : ℂ => principalZetaRegularFactor (1+s)) 0 := by
    have ho : AnalyticAt ℂ principalZetaRegularFactor (1+(0:ℂ)) := by
      simpa only [add_zero] using principalZetaRegularFactor_analyticAt_one
    exact ho.comp (f := fun s : ℂ => 1+s) (x := 0) (by fun_prop)
  have hz (a : ℂ) : AnalyticAt ℂ (fun s : ℂ => principalIdealZeta (2+a*s)) 0 := by
    have ho : AnalyticAt ℂ principalIdealZeta (2+a*(0:ℂ)) := by
      simpa only [mul_zero,add_zero] using
        (cubicTheta_principalZeta_analyticAt (s:=2) (by norm_num) (by norm_num))
    exact ho.comp (f := fun s : ℂ => 2+a*s) (x := 0) (by fun_prop)
  exact ((cubicThetaMassEulerPrefactor_analyticAt_zero.mul hr).mul (hz 3)).div (hz 2)
    (by simpa using cubicTheta_principalZeta_two_ne_zero)

lemma cubicThetaMassRegular_zero :
    cubicThetaMassRegular 0=(2*3^(8:ℂ))*(principalThetaConstant/(residueHeckeScale 1:ℂ)) := by
  rw [cubicThetaMassRegular,cubicThetaMassEulerPrefactor_zero]
  simp only [mul_zero,add_zero,principalZetaRegularFactor_one]
  exact mul_div_cancel_right₀ _ cubicTheta_principalZeta_two_ne_zero

lemma cubicThetaMassRegular_real {σ : ℝ} (hσ : 0 < σ) :
    cubicThetaMassRegular (σ:ℂ)=(σ:ℂ)*(cubicThetaCoefficientMass σ:ℂ) := by
  have hs0 : (1+(σ:ℂ))≠0 := by
    intro h
    have hr := congrArg Complex.re h
    simp only [Complex.add_re,Complex.one_re,Complex.ofReal_re,Complex.zero_re] at hr
    linarith
  have hs1 : (1+(σ:ℂ))≠1 := by
    intro h
    have hr := congrArg Complex.re h
    simp only [Complex.add_re,Complex.one_re,Complex.ofReal_re] at hr
    linarith
  rw [cubicThetaMassRegular,principalZetaRegularFactor_eq hs0 hs1,
    cubicThetaCoefficientMass_euler hσ]
  ring

theorem cubicThetaCoefficientMass_residue :
    Tendsto (fun σ : ℝ => (σ:ℂ)*(cubicThetaCoefficientMass σ:ℂ)) (𝓝[>] 0)
      (𝓝 ((2*3^(8:ℂ))*(principalThetaConstant/(residueHeckeScale 1:ℂ)))) := by
  have h := cubicThetaMassRegular_analyticAt_zero.continuousAt.tendsto.comp
    (Complex.continuous_ofReal.tendsto (0:ℝ))
  rw [cubicThetaMassRegular_zero] at h
  apply (h.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  exact cubicThetaMassRegular_real hσ

end CubicFirstMoment

end

end OAI
