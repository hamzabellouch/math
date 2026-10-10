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

section
open Set Filter Topology
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]

theorem flow_generator_commutes (a : ℝ → A) (d : A)
    (_ha0 : a 0=1) (ham : ∀ s t, a (s+t)=a s*a t) (hd : HasDerivAt a d 0) (s : ℝ) :
    d*a s=a s*d := by
  have h1 := hd.mul_const (a s)
  have h2 := hd.const_mul (a s)
  have he : (fun t => a t*a s)=(fun t => a s*a t) := by
    funext t; rw [←ham,←ham,add_comm]
  rw [he] at h1
  exact h1.unique h2

theorem bounded_complex_flow_generator_zero (a b : ℝ → A) (d : A)
    (ha0 : a 0=1) (hb0 : b 0=1) (ham : ∀ s t, a (s+t)=a s*a t)
    (hda : ∀ t, HasDerivAt a (d*a t) t)
    (hdb : ∀ t, HasDerivAt b ((Complex.I • d)*b t) t)
    (hbd : Bornology.IsBounded (Set.range (fun z : ℂ => a z.re*b z.im))) : d=0 := by
  let f : ℂ → A := fun z => a z.re*b z.im
  have hd0 : HasDerivAt a d 0 := by simpa only [ha0,mul_one] using hda 0
  have hc := flow_generator_commutes a d ha0 ham hd0
  have hf : Differentiable ℂ f := by
    intro z
    have hA := (hda z.re).hasFDerivAt.comp z Complex.reCLM.hasFDerivAt
    have hB := (hdb z.im).hasFDerivAt.comp z Complex.imCLM.hasFDerivAt
    have hR := hA.mul' hB
    let v := d*a z.re*b z.im
    have he : (ContinuousLinearMap.toSpanSingleton ℂ v).restrictScalars ℝ =
        (a z.re • ((ContinuousLinearMap.toSpanSingleton ℝ ((Complex.I • d)*b z.im)).comp
          Complex.imCLM)) +
        (MulOpposite.op (b z.im) • ((ContinuousLinearMap.toSpanSingleton ℝ (d*a z.re)).comp Complex.reCLM)) := by
      ext w
      change w • v = a z.re*(w.im • ((Complex.I • d)*b z.im)) +
        (w.re • (d*a z.re))*b z.im
      rw [mul_smul_comm,smul_mul_assoc,mul_smul_comm,←mul_assoc,←hc,
        smul_mul_assoc]
      change w • v=w.im • (Complex.I • v)+w.re • v
      rw [add_comm]
      calc
        w • v = ((w.re : ℂ)+(w.im : ℂ)*Complex.I) • v := by rw [Complex.re_add_im]
        _ = (w.re : ℂ) • v+(w.im : ℂ) • (Complex.I • v) := by rw [add_smul,mul_smul]
        _ = _ := congrArg₂ (fun u u' : A => u+u')
          (RCLike.real_smul_eq_coe_smul (K := ℂ) w.re v).symm
          (RCLike.real_smul_eq_coe_smul (K := ℂ) w.im (Complex.I • v)).symm
    exact (hasFDerivAt_of_restrictScalars (𝕜 := ℝ) hR he).differentiableAt
  have hconst (t : ℝ) : a t=1 := by
    have hh := hf.apply_eq_apply_of_bounded hbd (t : ℂ) 0
    simpa only [f,Complex.ofReal_re,Complex.ofReal_im,Complex.zero_re,Complex.zero_im,
      hb0,ha0,mul_one] using hh
  exact hd0.unique ((hasDerivAt_const (0 : ℝ) (1 : A)).congr_of_eventuallyEq
    (Eventually.of_forall hconst))
end

open Set Filter Topology
namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
include hU

theorem IsCompleteGenerator.eq_zero_of_I_smul {X : Affine n → Affine n}
    (hbd : Bornology.IsBounded U) (hX : IsCompleteGenerator U X)
    (hiX : IsCompleteGenerator U (Complex.I • X)) : X=0 := by
  obtain ⟨a,ha,ha0,ham,hXa⟩ := hX
  obtain ⟨b,hb,hb0,hbm,hXb⟩ := hiX
  have hba (x : Affine n) : infinitesimalGenerator b x=Complex.I • infinitesimalGenerator a x := by
    rw [hXb,hXa]
    rfl
  have hzero (p : U) : infinitesimalGenerator a p.val=0 := by
    let f : ℂ → Affine n := fun z =>
      ((a z.re).toHomeomorph ((b z.im).toHomeomorph p)).val
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
        rw [hba,ContinuousLinearMap.map_smul_of_tower, map_smul,
          ←infinitesimalGenerator_equivariant hU a ha hbd ha0 ham q z.re]
        change w • v=w.re • v+w.im • (Complex.I • v)
        exact Hermitian.complex_smul_split w v
      apply (hasFDerivAt_of_restrictScalars (𝕜 := ℝ) hR he).differentiableAt.congr_of_eventuallyEq
      filter_upwards [] with w
      exact (Biholomorph.ambientAut_apply (a w.re) ((b w.im).toHomeomorph p)).symm
    have hbounded : Bornology.IsBounded (Set.range f) :=
      hbd.subset (by rintro _ ⟨z,rfl⟩; exact ((a z.re).toHomeomorph ((b z.im).toHomeomorph p)).property)
    have hconst (t : ℝ) : ((a t).toHomeomorph p).val=p.val := by
      have hh := hf.apply_eq_apply_of_bounded hbounded (t : ℂ) 0
      simpa only [f,Complex.ofReal_re,Complex.ofReal_im,Complex.zero_re,Complex.zero_im,
        hb0,ha0,one_apply] using hh
    have hd := oneParameter_hasDerivAt_zero hU a ha hbd ha0 ham p
    exact hd.unique ((hasDerivAt_const (0 : ℝ) p.val).congr_of_eventuallyEq
      (Filter.Eventually.of_forall hconst))
  funext x
  change X x=0
  rw [←hXa]
  by_cases hx : x∈U
  · exact hzero ⟨x,hx⟩
  · exact infinitesimalGenerator_of_not_mem a hx

end Biholomorph
end Release061

end

end OAI
