import OAI.NumberTheory.CubicMoment.Estimates.PrincipalZetaContinuation

namespace OAI

/-! An analytic, nonzero numerator for the simple pole at one of the
actual principal ideal zeta function. -/
noncomputable section
open Filter
open scoped Topology
namespace CubicFirstMoment

def principalZetaPrefactor (s : ℂ) : ℂ :=
  (residueHeckeScale 1:ℂ)^(-s)*(Complex.Gamma s)⁻¹

lemma principalZetaPrefactor_differentiable : Differentiable ℂ principalZetaPrefactor := by
  let _ : NeZero (residueHeckeScale 1:ℂ) := ⟨Complex.ofReal_ne_zero.mpr
    (residueHeckeScale_pos (q := 1) one_ne_zero).ne'⟩
  exact ((differentiable_const_cpow_of_neZero (residueHeckeScale 1:ℂ)).comp
    differentiable_neg).mul Complex.differentiable_one_div_Gamma

def principalZetaRegularFactor (s : ℂ) : ℂ :=
  principalZetaPrefactor s*((s-1)*(principalIdealFEPair.Λ₀ s-principalThetaConstant/s)+
    principalThetaConstant)

lemma principalZetaRegularFactor_analyticAt_one : AnalyticAt ℂ principalZetaRegularFactor 1 := by
  unfold principalZetaRegularFactor
  apply (principalZetaPrefactor_differentiable.analyticAt 1).mul
  apply AnalyticAt.add
  · apply (analyticAt_id.sub analyticAt_const).mul
    exact (principalIdealFEPair.differentiable_Λ₀.analyticAt 1).sub
      (analyticAt_const.div analyticAt_id one_ne_zero)
  · exact analyticAt_const

lemma principalZetaRegularFactor_one :
    principalZetaRegularFactor 1=principalThetaConstant/(residueHeckeScale 1:ℂ) := by
  simp [principalZetaRegularFactor,principalZetaPrefactor,Complex.cpow_neg,
    div_eq_mul_inv,mul_comm]

lemma principalZetaRegularFactor_one_ne_zero : principalZetaRegularFactor 1 ≠ 0 := by
  rw [principalZetaRegularFactor_one]
  exact div_ne_zero principalThetaConstant_ne_zero (Complex.ofReal_ne_zero.mpr
    (residueHeckeScale_pos (q := 1) one_ne_zero).ne')

lemma principalZetaRegularFactor_eq {s : ℂ} (hs : s ≠ 0) (hs1 : s ≠ 1) :
    principalZetaRegularFactor s=(s-1)*principalIdealZeta s := by
  change principalZetaPrefactor s*((s-1)*(principalIdealFEPair.Λ₀ s-principalThetaConstant/s)+
    principalThetaConstant)=(s-1)*(principalZetaPrefactor s*
      (principalIdealFEPair.Λ₀ s-(1/s)*principalThetaConstant-
        (1/(1-s))*principalThetaConstant))
  have h1s : 1-s ≠ 0 := sub_ne_zero.mpr hs1.symm
  field_simp
  ring

theorem principalIdealZeta_residue_one :
    Tendsto (fun s : ℂ => (s-1)*principalIdealZeta s) (𝓝[≠] 1)
      (𝓝 (principalThetaConstant/(residueHeckeScale 1:ℂ))) := by
  have h := principalZetaRegularFactor_analyticAt_one.continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds : 𝓝[≠] (1:ℂ) ≤ 𝓝 1)
  rw [principalZetaRegularFactor_one] at h
  apply h.congr'
  filter_upwards [(eventually_ne_nhds (one_ne_zero: (1:ℂ) ≠ 0)).filter_mono
    (nhdsWithin_le_nhds : 𝓝[≠] (1:ℂ) ≤ 𝓝 1),self_mem_nhdsWithin] with s hs hs1
  exact principalZetaRegularFactor_eq hs hs1

end CubicFirstMoment

end

end OAI
