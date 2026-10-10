import Mathlib
import OAI.Analysis.SymmetricDomains.HolQuadraticSmul
import OAI.Analysis.SymmetricDomains.StrictModelSupports
import OAI.Analysis.SymmetricDomains.QuadraticDomainConnectedComponent
import OAI.Analysis.SymmetricDomains.SupportedWeightedLimit

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology Metric Complex
open scoped Classical

theorem supported_hermitian_weighted_model {r k N : ℕ}
    (B : Fin k → Affine r →ₗ[ℝ] Affine r →ₗ[ℝ] ℝ) (C : Set (Fin k → ℝ))
    (Φ : Affine r × Affine k → Affine N) (hΦ : AnalyticAt ℂ Φ 0)
    (hi : Function.Injective (fderiv ℂ Φ 0))
    (U : Set (Affine N))
    (hcover : ∀ z ∈ quadraticDomain (fun z i => B i z z) C,
      ∀ᶠ t : ℝ in 𝓝[>] 0, Φ (weightedScale t z) ∈ U)
    (h : Fin k → Affine N → ℂ) (hh : ∀ i, ContinuousAt (h i) (Φ 0))
    (hh0 : ∀ i, h i (Φ 0)=1)
    (hpeak : ∀ i y, y ∈ U → ‖h i y‖ ≤ Real.exp (-(‖y-Φ 0‖^2)))
    (ha : ∀ i, AnalyticAt ℂ (fun z => Complex.log (h i (Φ z))) 0)
    (β : Fin k → Fin k → ℝ) (hβ : LinearIndependent ℝ β)
    (hβeq : ∀ i z, fderiv ℂ (fun z => Complex.log (h i (Φ z))) 0 z =
      I*∑ j, (β i j : ℂ)*z.2 j) :
    ∃ (e : (Fin k → ℝ) ≃L[ℝ] (Fin k → ℝ)) (c : ℝ), 0 < c ∧
      ∀ z ∈ quadraticDomain (Hermitian.hermQuadratic B) C,
        ∀ i, c*‖z.1‖^2 ≤ e (fun j => (z.2 j).im) i := by
  have hx (i : Fin k) := supported_weighted_limit Φ hΦ U
    (quadraticDomain (fun z i => B i z z) C) hcover (h i) (hh i) (hh0 i)
    (hpeak i) (ha i) (β i) (hβeq i)
  choose A hA hAbound using hx
  let J : Affine r →ₗ[ℂ] Affine N := (fderiv ℂ Φ 0).toLinearMap.comp
    (LinearMap.inl ℂ (Affine r) (Affine k))
  have hJ : Function.Injective J := by
    intro z z' hz
    change fderiv ℂ Φ 0 (z,0)=fderiv ℂ Φ 0 (z',0) at hz
    exact congrArg Prod.fst (hi hz)
  obtain ⟨c,hc,hco⟩ := Hermitian.injective_squared_lower_bound J hJ
  let e := independentSupportCoordinates β hβ
  let P : Fin k → Affine r → ℂ := fun i z =>
    (∑ j, (β i j : ℂ)*Hermitian.holQuadratic B z j)-A i z
  have hP : ∀ i z, P i (I • z) = -P i z := by
    intro i z
    simp only [P,Hermitian.holQuadratic_smul,I_sq,neg_smul,one_smul,Pi.neg_apply,
      mul_neg,Finset.sum_neg_distrib,hA]
    ring
  have hbound : ∀ z ∈ quadraticDomain (Hermitian.hermQuadratic B) C,
      ∀ i, ‖J z.1‖^2 ≤ e (fun j => (z.2 j).im) i+(P i z.1).re := by
    intro z hz i
    let z' := (Hermitian.quadraticShear B).symm z
    have hz' : z' ∈ quadraticDomain (fun z i => B i z z) C := by
      have hr := Hermitian.quadraticShear_residual B z'
      change (fun i => (z'.2 i).im-B i z'.1 z'.1) ∈ C
      rw [← hr]
      change (fun i => (((Hermitian.quadraticShear B) ((Hermitian.quadraticShear B).symm z)).2 i).im-
        Hermitian.hermQuadratic B ((Hermitian.quadraticShear B) ((Hermitian.quadraticShear B).symm z)).1 i) ∈ C
      rw [(Hermitian.quadraticShear B).apply_symm_apply]
      exact hz
    have H := hAbound i z' hz'
    change ‖J z.1‖^2 ≤ (∑ j, β i j*(z.2 j+I*Hermitian.holQuadratic B z.1 j).im)-(A i z.1).re at H
    have he : (∑ j, β i j*(z.2 j+I*Hermitian.holQuadratic B z.1 j).im)-(A i z.1).re =
        e (fun j => (z.2 j).im) i+(P i z.1).re := by
      simp only [e,independentSupportCoordinates_apply,P,add_im,I_mul_im,mul_add,
        Finset.sum_add_distrib,sub_re,Complex.re_sum,mul_re,ofReal_re,ofReal_im,
        zero_mul,sub_zero]
      ring
    rw [he] at H
    exact H
  refine ⟨e,c,hc,?_⟩
  intro z hz i
  have hinv : ∀ x ∈ quadraticDomain (Hermitian.hermQuadratic B) C,
      (I • x.1,x.2) ∈ quadraticDomain (Hermitian.hermQuadratic B) C := by
    intro x hx
    exact (quadraticDomain_unit_rotation _ C I
      (fun z => Hermitian.hermQuadratic_unit B I norm_I z) x).mpr hx
  exact (hco z.1).trans (Hermitian.cancel_quadratic_support hinv J
    (fun w => e (fun j => (w j).im) i) (P i) (hP i)
      (fun z hz => hbound z hz i) z hz)

end Release061

end

end OAI
