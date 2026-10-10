import OAI.NumberTheory.CubicMoment.Theta.CubicThetaConstantDirichlet

namespace OAI

/-! Continuation of the actual zero-frequency scattering coefficient.
This does not assert continuation of the nonzero Fourier coefficients. -/
noncomputable section
open Filter
open scoped Topology
namespace CubicFirstMoment

def cubicThetaConstantContinuation (s : ℂ) : ℂ :=
  (2*(3:ℂ)^(3-3*s)/(1-(3:ℂ)^(2-3*s)))*
    principalIdealZeta (3*s-3)/principalIdealZeta (3*s-2)

theorem cubicThetaConstantContinuation_right {s : ℂ} (hs : 4/3<s.re) :
    cubicThetaConstantDirichlet s=cubicThetaConstantContinuation s := by
  have ht : 1<(3*s-3).re := by
    simp only [Complex.sub_re,Complex.mul_re,Complex.re_ofNat,Complex.im_ofNat,zero_mul,sub_zero]
    linarith
  rw [cubicThetaConstantDirichlet_eq_ramified hs,cubicThetaRamifiedDensitySeries_eq ht]
  rw [show -(3*s-3)=3-3*s by ring,show (3*s-3)+1=3*s-2 by ring,
    show -(3*s-2)=2-3*s by ring]
  unfold cubicThetaConstantContinuation
  ring

lemma cubicTheta_principalZeta_analyticAt {s : ℂ} (hs0 : s≠0) (hs1 : s≠1) :
    AnalyticAt ℂ principalIdealZeta s := by
  change AnalyticAt ℂ (fun z => principalZetaPrefactor z*
    (principalIdealFEPair.Λ₀ z-(1/z)*principalThetaConstant-
      (1/(1-z))*principalThetaConstant)) s
  apply (principalZetaPrefactor_differentiable.analyticAt s).mul
  apply AnalyticAt.sub
  · exact (principalIdealFEPair.differentiable_Λ₀.analyticAt s).sub
      ((analyticAt_const.div analyticAt_id hs0).mul analyticAt_const)
  · exact (analyticAt_const.div (analyticAt_const.sub analyticAt_id)
      (sub_ne_zero.mpr hs1.symm)).mul analyticAt_const

lemma cubicTheta_principalZeta_two_ne_zero : principalIdealZeta 2≠0 := by
  rw [principalIdealZeta_right (by norm_num : 1<(2:ℂ).re)]
  exact idealDirichlet_ne_zero (fun _ => (1:ℂ)) (by simp) rfl (by simp) (by norm_num)

def cubicThetaConstantRegular (s : ℂ) : ℂ :=
  (2*(3:ℂ)^(3-3*s)/(1-(3:ℂ)^(2-3*s))/principalIdealZeta (3*s-2))*
    (principalZetaRegularFactor (3*s-3)/3)

lemma cubicThetaConstantRegular_analyticAt :
    AnalyticAt ℂ cubicThetaConstantRegular (4/3:ℂ) := by
  let _ : NeZero (3:ℂ) := ⟨by norm_num⟩
  have ha (a b : ℂ) : AnalyticAt ℂ (fun z : ℂ => a*z+b) (4/3:ℂ) := by fun_prop
  have hp (a b : ℂ) : AnalyticAt ℂ (fun z : ℂ => (3:ℂ)^(a*z+b)) (4/3:ℂ) :=
    ((differentiable_const_cpow_of_neZero (3:ℂ)).analyticAt _).comp (f:=fun z : ℂ => a*z+b) (x:=(4/3:ℂ)) (ha a b)
  have hP : AnalyticAt ℂ (fun z : ℂ => (3:ℂ)^(3-3*z)) (4/3:ℂ) := by
    have he : (fun z : ℂ => (3:ℂ)^(3-3*z))=(fun z : ℂ => (3:ℂ)^(-3*z+3)) := by
      funext z
      congr 1
      ring
    rw [he]
    exact hp (-3) 3
  have hQ : AnalyticAt ℂ (fun z : ℂ => (3:ℂ)^(2-3*z)) (4/3:ℂ) := by
    have he : (fun z : ℂ => (3:ℂ)^(2-3*z))=(fun z : ℂ => (3:ℂ)^(-3*z+2)) := by
      funext z
      congr 1
      ring
    rw [he]
    exact hp (-3) 2
  have hZ : AnalyticAt ℂ (fun z : ℂ => principalIdealZeta (3*z-2)) (4/3:ℂ) := by
    have ho : AnalyticAt ℂ principalIdealZeta (3*(4/3:ℂ)-2) := by
      convert cubicTheta_principalZeta_analyticAt (s:=2) (by norm_num) (by norm_num) using 1; norm_num
    exact ho.comp (f:=fun z : ℂ => 3*z-2) (x:=(4/3:ℂ)) (by fun_prop)
  have hR : AnalyticAt ℂ (fun z : ℂ => principalZetaRegularFactor (3*z-3)) (4/3:ℂ) := by
    have ho : AnalyticAt ℂ principalZetaRegularFactor (3*(4/3:ℂ)-3) := by
      convert principalZetaRegularFactor_analyticAt_one using 1; norm_num
    exact ho.comp (f:=fun z : ℂ => 3*z-3) (x:=(4/3:ℂ)) (by fun_prop)
  have hden : 1-(3:ℂ)^(2-3*(4/3:ℂ))≠0 := by
    norm_num [Complex.cpow_neg,Complex.cpow_ofNat]
  have hzne : principalIdealZeta (3*(4/3:ℂ)-2)≠0 := by
    convert cubicTheta_principalZeta_two_ne_zero using 1; norm_num
  exact (((analyticAt_const.mul hP).div (analyticAt_const.sub hQ) hden).div hZ hzne).mul
    (hR.div analyticAt_const (by norm_num))

lemma cubicThetaConstantRegular_eq {s : ℂ} (hs0 : 3*s-3≠0) (hs1 : 3*s-3≠1) :
    cubicThetaConstantRegular s=(s-4/3)*cubicThetaConstantContinuation s := by
  rw [cubicThetaConstantRegular,principalZetaRegularFactor_eq hs0 hs1,
    cubicThetaConstantContinuation]
  ring

lemma cubicThetaConstantRegular_value :
    cubicThetaConstantRegular (4/3:ℂ)=
      (principalThetaConstant/(residueHeckeScale 1:ℂ))/(4*principalIdealZeta 2) := by
  unfold cubicThetaConstantRegular
  norm_num [principalZetaRegularFactor_one,Complex.cpow_neg,Complex.cpow_ofNat]
  ring

theorem cubicThetaConstantContinuation_residue :
    Tendsto (fun s : ℂ => (s-4/3)*cubicThetaConstantContinuation s) (𝓝[≠] (4/3:ℂ))
      (𝓝 ((principalThetaConstant/(residueHeckeScale 1:ℂ))/(4*principalIdealZeta 2))) := by
  have h := cubicThetaConstantRegular_analyticAt.continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds : 𝓝[≠] (4/3:ℂ)≤𝓝 (4/3:ℂ))
  rw [cubicThetaConstantRegular_value] at h
  apply h.congr'
  have hn : ∀ᶠ s : ℂ in 𝓝[≠] (4/3:ℂ), s≠1 :=
    (eventually_ne_nhds (by norm_num : (4/3:ℂ)≠1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hn,self_mem_nhdsWithin] with s hs hs'
  change s≠(4/3:ℂ) at hs'
  apply cubicThetaConstantRegular_eq
  · intro he
    apply hs
    linear_combination (1/3:ℂ)*he
  · intro he
    apply hs'
    linear_combination (1/3:ℂ)*he

end CubicFirstMoment

end

end OAI
