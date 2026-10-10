import OAI.Geometry.RCD.Sobolev.HessianActionProduct
import OAI.Geometry.RCD.Heat.LocalLogarithmicLaplacian

namespace OAI

/-! # The Hessian chain rule in a gradient direction

The second scalar derivative cancels in the three-term action. Only the
two existing bounded mixed Gram representatives are needed.
-/

open Set Filter MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (Q : QuadraticCheegerEnergy μ)

theorem localHessianAction_comp_direction {Ω : Set X}
    (f a u fa fu au : SobolevSpace μ Q)
    {φ ψ χ : ℝ → ℝ} {C D : ℝ≥0}
    (hφ : LipschitzWith C φ) (hψ : LipschitzWith D ψ)
    (hφ0 : φ 0=0) (hψ0 : ψ 0=0) (hχ : Continuous χ)
    (hdφ : ∀ z, HasDerivAt φ (ψ z) z) (hdψ : ∀ z, HasDerivAt ψ (χ z) z)
    (B E M N : ℝ≥0) (hB : ∀ z, |ψ z| ≤ B) (hE : ∀ z, |χ z| ≤ E)
    (hfuB : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q fu x| ≤ M)
    (hauB : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q au x| ≤ N)
    (hfu : SobolevSpace.toLp μ Q fu =ᵐ[μ.restrict Ω] localGamma μ Q f u)
    (hau : SobolevSpace.toLp μ Q au =ᵐ[μ.restrict Ω] localGamma μ Q a u) :
    let U := SobolevSpace.comp μ Q hφ hφ0 u
    let P := SobolevSpace.comp μ Q hψ hψ0 u
    localHessianAction μ Q f a U fa
      (SobolevSpace.product μ Q P fu B M) (SobolevSpace.product μ Q P au B N)
      =ᵐ[μ.restrict Ω] fun x => ψ (SobolevSpace.toLp μ Q u x)*
        localHessianAction μ Q f a u fa fu au x := by
  intro U P
  have hP : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q P x| ≤ B := by
    filter_upwards [SobolevSpace.comp_coe μ Q hψ hψ0 u] with x hx
    exact hx ▸ hB _
  filter_upwards [
    ae_restrict_of_ae (localGamma_product_right μ Q a P fu B M hP hfuB),
    ae_restrict_of_ae (localGamma_product_right μ Q f P au B N hP hauB),
    ae_restrict_of_ae (localGamma_comp_C1 μ Q u fa hφ hφ0 hψ.continuous hdφ B hB),
    ae_restrict_of_ae (localGamma_comp_C1_right μ Q a u hψ hψ0 hχ hdψ E hE),
    ae_restrict_of_ae (localGamma_comp_C1_right μ Q f u hψ hψ0 hχ hdψ E hE),
    ae_restrict_of_ae (SobolevSpace.comp_coe μ Q hψ hψ0 u),hfu,hau]
    with x h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈
  change SobolevSpace.toLp μ Q P x=ψ (SobolevSpace.toLp μ Q u x) at h₆
  change localGamma μ Q U fa x=_ at h₃
  change localGamma μ Q a P x=_ at h₄
  change localGamma μ Q f P x=_ at h₅
  dsimp only [localHessianAction]
  rw [h₁,h₂,h₃,h₄,h₅,h₆,h₇,h₈]
  ring

theorem exists_local_hessian_log_direction {Ω : Set X}
    (f a u fa fu au : SobolevSpace μ Q) (M N : ℝ≥0)
    (hfuB : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q fu x| ≤ M)
    (hauB : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q au x| ≤ N)
    (hfu : SobolevSpace.toLp μ Q fu =ᵐ[μ.restrict Ω] localGamma μ Q f u)
    (hau : SobolevSpace.toLp μ Q au =ᵐ[μ.restrict Ω] localGamma μ Q a u)
    {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d)
    (hu : ∀ᵐ x ∂μ.restrict Ω, SobolevSpace.toLp μ Q u x ∈ Icc c d) :
    ∃ U fU aU : SobolevSpace μ Q,
      (SobolevSpace.toLp μ Q U =ᵐ[μ.restrict Ω]
        fun x => Real.log (SobolevSpace.toLp μ Q u x)) ∧
      (SobolevSpace.toLp μ Q fU =ᵐ[μ.restrict Ω] localGamma μ Q f U) ∧
      (SobolevSpace.toLp μ Q aU =ᵐ[μ.restrict Ω] localGamma μ Q a U) ∧
      (∃ A : ℝ≥0, ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q fU x| ≤ A) ∧
      (∃ A : ℝ≥0, ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q aU x| ≤ A) ∧
      localHessianAction μ Q f a U fa fU aU =ᵐ[μ.restrict Ω] fun x =>
        localHessianAction μ Q f a u fa fu au x/SobolevSpace.toLp μ Q u x := by
  obtain ⟨φ,ψ,χ,C,D,B,E,hφ,hψ,hχ,hφ0,hψ0,hdφ,hdψ,hB,hE,he⟩ :=
    exists_local_smooth_log hc hcd
  let U := SobolevSpace.comp μ Q hφ hφ0 u
  let P := SobolevSpace.comp μ Q hψ hψ0 u
  let fU := SobolevSpace.product μ Q P fu B M
  let aU := SobolevSpace.product μ Q P au B N
  have hP : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q P x| ≤ B := by
    filter_upwards [SobolevSpace.comp_coe μ Q hψ hψ0 u] with x hx
    exact hx ▸ hB _
  have hfU := SobolevSpace.product_coe μ Q P fu B M hP hfuB
  have haU := SobolevSpace.product_coe μ Q P au B N hP hauB
  refine ⟨U,fU,aU,?_,?_,?_,?_,?_,?_⟩
  · filter_upwards [ae_restrict_of_ae (SobolevSpace.comp_coe μ Q hφ hφ0 u),hu]
      with x hx hu
    exact hx.trans (he _ hu).1
  · filter_upwards [ae_restrict_of_ae hfU,hfu,
      ae_restrict_of_ae (SobolevSpace.comp_coe μ Q hψ hψ0 u),
      ae_restrict_of_ae (localGamma_comp_C1_right μ Q f u hφ hφ0 hψ.continuous hdφ B hB)]
      with x hx hfx hpx hcx
    exact hx.trans (by rw [hfx,hpx]; exact hcx.symm)
  · filter_upwards [ae_restrict_of_ae haU,hau,
      ae_restrict_of_ae (SobolevSpace.comp_coe μ Q hψ hψ0 u),
      ae_restrict_of_ae (localGamma_comp_C1_right μ Q a u hφ hφ0 hψ.continuous hdφ B hB)]
      with x hx hax hpx hcx
    exact hx.trans (by rw [hax,hpx]; exact hcx.symm)
  · refine ⟨B*M,?_⟩
    filter_upwards [hfU,hP,hfuB] with x hx hp hf
    rw [hx,abs_mul]
    exact mul_le_mul hp hf (abs_nonneg _) B.coe_nonneg
  · refine ⟨B*N,?_⟩
    filter_upwards [haU,hP,hauB] with x hx hp hf
    rw [hx,abs_mul]
    exact mul_le_mul hp hf (abs_nonneg _) B.coe_nonneg
  · filter_upwards [localHessianAction_comp_direction μ Q f a u fa fu au
      hφ hψ hφ0 hψ0 hχ hdφ hdψ B E M N hB hE hfuB hauB hfu hau,hu]
      with x hx hu
    rw [hx,(he _ hu).2.1,div_eq_mul_inv,mul_comm]

end RegularPointCoordinates

end

end OAI
