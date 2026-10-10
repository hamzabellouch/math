import Mathlib
import OAI.Analysis.SymmetricDomains.ContinuousAutTransport

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
namespace Release061
open Set Filter Topology
namespace Biholomorph
open scoped Classical
variable {n m : ℕ} {U : Set (Affine n)} {D : Set (Affine m)}

def ambientMap (e : Biholomorph U D) : Affine n → Affine m :=
  ambientExtend (fun p => (e.toHomeomorph p).val)

@[simp] theorem ambientMap_apply (e : Biholomorph U D) (p : U) :
    e.ambientMap p.val=(e.toHomeomorph p).val := ambientExtend_apply _ p

 theorem ambientMap_analytic (hU : IsOpen U) (e : Biholomorph U D) :
    AnalyticOnNhd ℂ e.ambientMap U := e.holomorphic_toFun.analyticOnNhd_extend hU

 def mapDerivative (e : Biholomorph U D) (p : U) : Affine n →L[ℂ] Affine m :=
  fderiv ℂ e.ambientMap p.val

 theorem mapDerivative_symm_comp (hU : IsOpen U) (hD : IsOpen D)
    (e : Biholomorph U D) (p : U) :
    (e.symm.mapDerivative (e.toHomeomorph p)).comp (e.mapDerivative p)=
      ContinuousLinearMap.id ℂ (Affine n) := by
  have hi := (e.symm.ambientMap_analytic hD _ (e.toHomeomorph p).property).differentiableAt.hasFDerivAt
  rw [←ambientMap_apply e p] at hi
  have hcomp := hi.comp p.val ((e.ambientMap_analytic hU _ p.property).differentiableAt.hasFDerivAt)
  have heq : e.symm.ambientMap ∘ e.ambientMap =ᶠ[𝓝 p.val] id := by
    filter_upwards [hU.mem_nhds p.property] with x hx
    rw [Function.comp_apply,ambientMap_apply _ ⟨x,hx⟩,ambientMap_apply]
    exact congrArg Subtype.val (e.toHomeomorph.symm_apply_apply ⟨x,hx⟩)
  have hh := hcomp.congr_of_eventuallyEq heq.symm
  simpa only [ambientMap_apply,Function.comp_def,mapDerivative] using hh.unique (hasFDerivAt_id p.val)

def mapDerivativeEquiv (hU : IsOpen U) (hD : IsOpen D)
    (e : Biholomorph U D) (p : U) : Affine n ≃L[ℂ] Affine m :=
  ContinuousLinearEquiv.equivOfInverse (e.mapDerivative p)
    (e.symm.mapDerivative (e.toHomeomorph p))
    (by
      intro v
      exact congrArg (fun L : Affine n →L[ℂ] Affine n => L v)
        (mapDerivative_symm_comp hU hD e p))
    (by
        intro v
        have h := mapDerivative_symm_comp hD hU e.symm (e.toHomeomorph p)
        change (e.mapDerivative (e.toHomeomorph.symm (e.toHomeomorph p))).comp
          (e.symm.mapDerivative (e.toHomeomorph p))=ContinuousLinearMap.id ℂ (Affine m) at h
        rw [e.toHomeomorph.symm_apply_apply] at h
        exact congrArg (fun L : Affine m →L[ℂ] Affine m => L v) h)

@[simp] theorem mapDerivativeEquiv_apply (hU : IsOpen U) (hD : IsOpen D)
    (e : Biholomorph U D) (p : U) (v : Affine n) :
    mapDerivativeEquiv hU hD e p v=e.mapDerivative p v := rfl

def coordinateField (e : Biholomorph U D) (X : Affine n → Affine n)
    (x : Affine m) : Affine m :=
  if hx : x∈D then e.mapDerivative (e.toHomeomorph.symm ⟨x,hx⟩)
    (X (e.toHomeomorph.symm ⟨x,hx⟩).val) else 0

@[simp] theorem coordinateField_apply (e : Biholomorph U D) (X : Affine n → Affine n)
    (p : D) : coordinateField e X p.val=
      e.mapDerivative (e.toHomeomorph.symm p) (X (e.toHomeomorph.symm p).val) := by
  simp only [coordinateField,dite_eq_left p.property]

 theorem coordinateField_symm_cancel (hU : IsOpen U) (hD : IsOpen D)
    (e : Biholomorph U D) (X : Affine n → Affine n)
    (hX : ∀ x, x∉U → X x=0) : coordinateField e.symm (coordinateField e X)=X := by
  funext x
  by_cases hx : x∈U
  · rw [coordinateField_apply _ _ ⟨x,hx⟩,coordinateField_apply]
    change e.symm.mapDerivative (e.toHomeomorph ⟨x,hx⟩)
      (e.mapDerivative (e.toHomeomorph.symm (e.toHomeomorph ⟨x,hx⟩))
        (X (e.toHomeomorph.symm (e.toHomeomorph ⟨x,hx⟩)).val))=X x
    rw [e.toHomeomorph.symm_apply_apply]
    exact congrArg (fun L : Affine n →L[ℂ] Affine n => L (X x))
      (mapDerivative_symm_comp hU hD e ⟨x,hx⟩)
  · simp only [coordinateField,dite_eq_right hx,hX x hx]

 theorem infinitesimalGenerator_autTransport (hU : IsOpen U) [LocallyCompactSpace U]
    (hbd : Bornology.IsBounded U) (e : Biholomorph U D)
    (a : ℝ → Biholomorph U U) (ha : Continuous a) (ha0 : a 0=1)
    (ham : ∀ s t, a (s+t)=a s*a t) :
    infinitesimalGenerator (fun t => autTransport e (a t))=
      coordinateField e (infinitesimalGenerator a) := by
  funext x
  by_cases hx : x∈D
  · let y : U := e.toHomeomorph.symm ⟨x,hx⟩
    have hy : (a 0).ambientAut y.val=y.val := by rw [ha0,ambientAut_apply,one_apply]
    have hq : HasFDerivAt e.ambientMap ((e.mapDerivative y).restrictScalars ℝ)
        ((a 0).ambientAut y.val) := by
      rw [hy]
      exact ((e.ambientMap_analytic hU y.val y.property).differentiableAt.hasFDerivAt).restrictScalars ℝ
    have hcomp := hq.comp_hasDerivAt 0 (infinitesimalGenerator_hasDerivAt hU hbd a ha ha0 ham y.val)
    have heq : (fun t => e.ambientMap ((a t).ambientAut y.val))=
        (fun t => (autTransport e (a t)).ambientAut x) := by
      funext t
      rw [ambientAut_apply (autTransport e (a t)) ⟨x,hx⟩,
        ambientAut_apply,ambientMap_apply]
      rfl
    change HasDerivAt (fun t => e.ambientMap ((a t).ambientAut y.val))
      ((e.mapDerivative y) (infinitesimalGenerator a y.val)) 0 at hcomp
    rw [heq] at hcomp
    change deriv (fun t => (autTransport e (a t)).ambientAut x) 0=_
    rw [hcomp.deriv,coordinateField,dite_eq_left hx]
  · rw [infinitesimalGenerator_of_not_mem _ hx,coordinateField,dite_eq_right hx]

 theorem IsCompleteGenerator.coordinateField (hU : IsOpen U) [LocallyCompactSpace U]
    (hbd : Bornology.IsBounded U) (e : Biholomorph U D)
    {X : Affine n → Affine n} (hX : IsCompleteGenerator U X) :
    IsCompleteGenerator D (coordinateField e X) := by
  obtain ⟨a,ha,ha0,ham,hXa⟩ := hX
  refine ⟨fun t => autTransport e (a t),(continuous_autTransport e).comp ha,
    by simp only [ha0,autTransport_one],?_,?_⟩
  · intro s t; simp only [ham,autTransport_mul]
  · rw [infinitesimalGenerator_autTransport hU hbd e a ha ha0 ham,hXa]

end Biholomorph
end Release061

end

end OAI
