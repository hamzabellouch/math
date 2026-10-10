import Mathlib
import OAI.Analysis.SymmetricDomains.HermPartUnit
import OAI.Analysis.SymmetricDomains.FieldSecondJet

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
open Set Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Polynomial
open Filter Topology
namespace Release061
open Set Filter Topology
namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
    (hbd : Bornology.IsBounded U)
include hU hbd

theorem pushForwardGenerator_eq_of_bracket_zero
    (a : ℝ → Biholomorph U U) (ha : Continuous a)
    (ha0 : a 0=1) (ham : ∀ s t, a (s+t)=a s*a t)
    {Y : Affine n → Affine n} (hY : IsCompleteGenerator U Y)
    (hbr : VectorField.lieBracket ℂ (infinitesimalGenerator a) Y=0) (s : ℝ) :
    pushForwardGenerator (a s) Y=Y := by
  funext x
  by_cases hx : x∈U
  · have hd (t : ℝ) : HasDerivAt (fun r => pushForwardGenerator (a r) Y x) 0 t := by
      let q : U := (a t).toHomeomorph.symm ⟨x,hx⟩
      have h0 := pushForwardGenerator_hasDerivAt_zero hU hbd a ha ha0 ham Y
        (hY.analyticOnNhd hU hbd) q.val q.property
      rw [hbr,Pi.zero_apply,neg_zero] at h0
      have hs : HasDerivAt (fun r => pushForwardGenerator (a (r-t)) Y q.val) 0 t := by
        have h0' : HasDerivAt (fun r => pushForwardGenerator (a r) Y q.val) 0 (t-t) :=
          sub_self t ▸ h0
        convert h0'.scomp t (h := fun r : ℝ => r-t) ((hasDerivAt_id t).sub_const t) using 1 <;> first | rfl | exact (smul_zero _).symm
      have hh := (((a t).derivativeAt q).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hs
      rw [map_zero] at hh
      apply hh.congr_of_eventuallyEq
      filter_upwards [] with r
      change pushForwardGenerator (a r) Y x =
        (a t).derivativeAt q (pushForwardGenerator (a (r-t)) Y q.val)
      rw [←pushForwardGenerator_apply (a t) _ ⟨x,hx⟩,←pushForwardGenerator_mul hU,
        ←ham,add_sub_cancel]
    have he := is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt)
      (fun t => (hd t).deriv) s 0
    rw [ha0,pushForwardGenerator_one hU (fun _ hz => hY.eq_zero_of_not_mem hz)] at he
    exact he
  · rw [pushForwardGenerator,dite_eq_right hx,hY.eq_zero_of_not_mem hx]

 theorem generator_cross_equivariant
    (a : ℝ → Biholomorph U U) (ha : Continuous a)
    (ha0 : a 0=1) (ham : ∀ s t, a (s+t)=a s*a t)
    {Y : Affine n → Affine n} (hY : IsCompleteGenerator U Y)
    (hbr : VectorField.lieBracket ℂ (infinitesimalGenerator a) Y=0)
    (p : U) (t : ℝ) :
    Y ((a t).toHomeomorph p).val=(a t).derivativeAt p (Y p.val) := by
  have he := congrFun (pushForwardGenerator_eq_of_bracket_zero hU hbd a ha ha0 ham hY hbr t)
    ((a t).toHomeomorph p).val
  rw [pushForwardGenerator_apply] at he
  simpa only [Homeomorph.symm_apply_apply] using he.symm

theorem commuting_generators_value_zero
    (a b : ℝ → Biholomorph U U) (ha : Continuous a) (hb : Continuous b)
    (ha0 : a 0=1) (ham : ∀ s t, a (s+t)=a s*a t)
    (hb0 : b 0=1) (hbm : ∀ s t, b (s+t)=b s*b t)
    (hbr : VectorField.lieBracket ℂ (infinitesimalGenerator b) (infinitesimalGenerator a)=0)
    (p : U) (hrel : infinitesimalGenerator b p.val=Complex.I • infinitesimalGenerator a p.val) :
    infinitesimalGenerator a p.val=0 := by
  let f : ℂ → Affine n := fun z =>
    ((a z.re).toHomeomorph ((b z.im).toHomeomorph p)).val
  have hba (t : ℝ) : infinitesimalGenerator b ((b t).toHomeomorph p).val=
      Complex.I • infinitesimalGenerator a ((b t).toHomeomorph p).val := by
    rw [infinitesimalGenerator_equivariant hU b hb hbd hb0 hbm p t,hrel,map_smul,
      generator_cross_equivariant hU hbd b hb hb0 hbm ⟨a,ha,ha0,ham,rfl⟩ hbr p t]
  have hf : Differentiable ℂ f := by
    intro z
    let q : U := (b z.im).toHomeomorph p
    let v : Affine n := infinitesimalGenerator a ((a z.re).toHomeomorph q).val
    have hB := ((oneParameter_orbit_ODE hU b hb hbd hb0 hbm p z.im).hasFDerivAt).comp z
      Complex.imCLM.hasFDerivAt
    have hA := (oneParameter_joint_hasStrictFDerivAt hU a ha hbd ha0 ham z.re q).hasFDerivAt
    have hR := hA.comp z (Complex.reCLM.hasFDerivAt.prodMk hB)
    have he : (ContinuousLinearMap.toSpanSingleton ℂ v).restrictScalars ℝ =
        ((ContinuousLinearMap.toSpanSingleton ℝ v).coprod
          (((a z.re).derivativeAt q).restrictScalars ℝ)).comp
          (Complex.reCLM.prod ((ContinuousLinearMap.toSpanSingleton ℝ
            (infinitesimalGenerator b q.val)).comp Complex.imCLM)) := by
      apply ContinuousLinearMap.ext
      intro w
      simp only [ContinuousLinearMap.toSpanSingleton_apply,ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.coprod_apply,ContinuousLinearMap.prod_apply,
        Complex.reCLM_apply,Complex.imCLM_apply]
      change w • v = w.re • v + ((a z.re).derivativeAt q)
        (w.im • infinitesimalGenerator b q.val)
      rw [hba,ContinuousLinearMap.map_smul_of_tower,map_smul,
        ←infinitesimalGenerator_equivariant hU a ha hbd ha0 ham q z.re]
      exact Hermitian.complex_smul_split w v
    apply (hasFDerivAt_of_restrictScalars (𝕜 := ℝ) hR he).differentiableAt.congr_of_eventuallyEq
    filter_upwards [] with w
    exact (ambientAut_apply (a w.re) ((b w.im).toHomeomorph p)).symm
  have hbounded : Bornology.IsBounded (Set.range f) := hbd.subset
    (by rintro _ ⟨z,rfl⟩; exact ((a z.re).toHomeomorph ((b z.im).toHomeomorph p)).property)
  have hconst (t : ℝ) : ((a t).toHomeomorph p).val=p.val := by
    have hh := hf.apply_eq_apply_of_bounded hbounded (t : ℂ) 0
    simpa only [f,Complex.ofReal_re,Complex.ofReal_im,Complex.zero_re,Complex.zero_im,
      hb0,ha0,one_apply] using hh
  exact (oneParameter_hasDerivAt_zero hU a ha hbd ha0 ham p).unique
    ((hasDerivAt_const (0 : ℝ) p.val).congr_of_eventuallyEq (Eventually.of_forall hconst))
end Biholomorph
end Release061

end

end OAI
