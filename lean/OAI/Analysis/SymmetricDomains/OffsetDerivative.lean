import Mathlib
import OAI.Analysis.SymmetricDomains.GenericSurjectiveRealNormal

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

section
open Set Filter Topology
open scoped Classical
variable {E S V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

noncomputable def graphOffsetDifferentialEquiv (L : S →L[ℝ] V) :
    (S × V) ≃L[ℝ] (S × V) := by
  let P := ContinuousLinearMap.fst ℝ S V
  let Q := ContinuousLinearMap.snd ℝ S V
  refine ContinuousLinearEquiv.equivOfInverse (P.prod (Q-L.comp P))
    (P.prod (Q+L.comp P)) ?_ ?_
  · intro p
    apply Prod.ext
    · rfl
    · change p.2-L p.1+L p.1=p.2
      exact sub_add_cancel _ _
  · intro p
    apply Prod.ext
    · rfl
    · change p.2+L p.1-L p.1=p.2
      exact add_sub_cancel_right _ _

@[simp] theorem graphOffsetDifferentialEquiv_apply (L : S →L[ℝ] V) (p : S × V) :
    graphOffsetDifferentialEquiv L p = (p.1,p.2-L p.1) := rfl

variable [CompleteSpace E] [CompleteSpace S] [CompleteSpace V]

theorem offset_coordinate_local_inverse (C : E ≃L[ℝ] (S × V))
    (φ : S → V) {s : S} (hφ : AnalyticAt ℝ φ s) :
    ∃ e : OpenPartialHomeomorph E (S × V),
      (e : E → S × V) = (fun z => let u := C (z+C.symm (s,φ s)); (u.1,u.2-φ u.1)) ∧
      (0 : E) ∈ e.source ∧ e 0 = (s,0) ∧ AnalyticAt ℝ e.symm (s,0) ∧
      AnalyticAt ℝ e 0 := by
  let a := C.symm (s,φ s)
  let f : E → S × V := fun z => let u := C (z+a); (u.1,u.2-φ u.1)
  have hCa : C ((0 : E)+a) = (s,φ s) := by simp only [zero_add,a,C.apply_symm_apply]
  have hf0 : f 0 = (s,0) := by simp only [f,hCa,sub_self]
  have hC : AnalyticAt ℝ (fun z : E => C (z+a)) 0 :=
    (C.toContinuousLinearMap.analyticAt _).comp (analyticAt_id.add analyticAt_const)
  have hφ' : AnalyticAt ℝ φ (C ((0 : E)+a)).1 := by simpa only [hCa] using hφ
  have hPa : AnalyticAt ℝ (fun z : E => (C (z+a)).1) 0 := analyticAt_fst.comp hC
  have hQa : AnalyticAt ℝ (fun z : E => (C (z+a)).2) 0 := analyticAt_snd.comp hC
  have hf : AnalyticAt ℝ f 0 :=
    hPa.prod (hQa.sub (hφ'.comp (f := fun z : E => (C (z+a)).1) (x := 0) hPa))
  let L := C.trans (graphOffsetDifferentialEquiv (fderiv ℝ φ s))
  have hCd : HasFDerivAt (fun z : E => C (z+a)) C.toContinuousLinearMap 0 :=
    C.toContinuousLinearMap.hasFDerivAt.comp 0 ((hasFDerivAt_id 0).add_const a)
  have hP := hasFDerivAt_fst.comp 0 hCd
  have hQ := hasFDerivAt_snd.comp 0 hCd
  have hφd : HasFDerivAt φ (fderiv ℝ φ s) (C ((0 : E)+a)).1 := by
    simpa only [hCa] using hφ.differentiableAt.hasFDerivAt
  have hd : HasFDerivAt f (L : E →L[ℝ] (S × V)) 0 := by
    convert hP.prodMk (hQ.sub (hφd.comp 0 hP)) using 1 <;> rfl
  obtain ⟨e,he,hes,hea⟩ := real_analytic_local_inverse hf L hd
  exact ⟨e,he,hes,by simpa only [he] using hf0,by simpa only [hf0] using hea,he.symm ▸ hf⟩
end

open Set Filter Topology Metric
open scoped Classical

structure NashBoundaryScalingChart {d m N : ℕ} {U V : Set (Affine N)}
    {B : Set (Fin d → ℝ)} {q : (Fin d → ℝ) → Affine N}
    (c : NashBoundaryChart (m := m) U V B q) (x : Fin d → ℝ) where
  tangentDim : ℕ
  normalDim : ℕ
  dimension : tangentDim+normalDim=m
  normal_dimension : normalDim=c.normal.normalDim
  coordinates : Affine m ≃L[ℂ] (Affine tangentDim × Affine normalDim)
  normalMap : (Fin normalDim → ℝ) ≃L[ℝ] (Fin c.normal.normalDim → ℝ)
  differential : ∀ z, c.oldOffsetDerivative (c.normal.parameters x) (coordinates.symm z) =
    normalMap (Flatten.imaginaryPart normalDim z.2)
  offsets : OpenPartialHomeomorph (Affine tangentDim × Affine normalDim)
    ((Fin ((c.normal.tangentDim+c.normal.tangentDim)+c.normal.normalDim) → ℝ) × (Fin c.normal.normalDim → ℝ))
  offsets_eq : ∀ z, offsets z =
    (c.oldParameter (coordinates.symm z+c.oldPosition (c.normal.parameters x)),
     c.oldOffset (coordinates.symm z+c.oldPosition (c.normal.parameters x)))
  source_zero : (0 : Affine tangentDim × Affine normalDim) ∈ offsets.source
  offsets_zero : offsets 0 = (c.normal.parameters x,0)
  inverse_analytic : AnalyticAt ℝ offsets.symm (c.normal.parameters x,0)
  analytic : AnalyticAt ℝ offsets 0

namespace NashBoundaryChart
variable {d m N : ℕ} {U V : Set (Affine N)} {B : Set (Fin d → ℝ)}
variable {q : (Fin d → ℝ) → Affine N}

theorem scaling_chart (c : NashBoundaryChart (m := m) U V B q) {x}
    (hgood : c.GoodAt x) (hq : DifferentiableAt ℝ q x)
    (hqi : Function.Injective (fderiv ℝ q x))
    (hr : m ≤ Matrix.rank (fun j i => fderiv ℝ (fun y => q y j) x (Pi.single i 1))) :
    Nonempty (NashBoundaryScalingChart c x) := by
  obtain ⟨r,l,e,L,hd,hl,hL⟩ := generic_surjective_real_normal_form
    (c.oldOffsetDerivative (c.normal.parameters x)) (c.oldOffsetDerivative_surjective _)
    (c.oldOffsetDerivative_generic hgood hq hqi hr)
  let C : (Affine r × Affine l) ≃L[ℝ] _ :=
    ((e.symm.toLinearEquiv.restrictScalars ℝ).toContinuousLinearEquiv).trans c.normal.realCoordinates
  obtain ⟨T,hT,hTs,hT0,hTin,hTa⟩ := offset_coordinate_local_inverse C c.normal.graph
    (c.normal.graph_analytic (c.normal.parameters x) (ball_subset_ball c.graphRadius_le hgood.2.1))
  refine ⟨⟨r,l,hd,hl,e,L,hL,T,?_,hTs,hT0,hTin,hTa⟩⟩
  intro z
  rw [hT]
  change (c.oldParameter (e.symm (z+e (c.oldPosition (c.normal.parameters x)))),
    c.oldOffset (e.symm (z+e (c.oldPosition (c.normal.parameters x))))) = _
  rw [map_add,e.symm_apply_apply]
end NashBoundaryChart

namespace NashBoundaryScalingChart
variable {d m N : ℕ} {U V : Set (Affine N)} {B : Set (Fin d → ℝ)}
variable {q : (Fin d → ℝ) → Affine N} {c : NashBoundaryChart (m := m) U V B q}
variable {x : Fin d → ℝ}

theorem offset_derivative (s : NashBoundaryScalingChart c x) (hgood : c.GoodAt x)
    (z : Affine s.tangentDim × Affine s.normalDim) :
    fderiv ℝ (fun y => (s.offsets y).2) 0 z = s.normalMap (Flatten.imaginaryPart s.normalDim z.2) := by
  let a := c.oldPosition (c.normal.parameters x)
  let f : (Affine s.tangentDim × Affine s.normalDim) → Affine m := fun y => s.coordinates.symm y+a
  have hf : HasFDerivAt f (s.coordinates.symm.toContinuousLinearMap.restrictScalars ℝ) 0 :=
    (s.coordinates.symm.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.add_const a
  have hD : HasFDerivAt c.oldOffset (c.oldOffsetDerivative (c.normal.parameters x)) (f 0) := by
    simpa only [f,map_zero,zero_add] using c.oldOffset_hasFDerivAt hgood.2.1
  have he : (fun y => (s.offsets y).2) = c.oldOffset ∘ f := by
    funext y
    rw [s.offsets_eq]
    rfl
  rw [he,(hD.comp 0 hf).fderiv]
  exact s.differential z
end NashBoundaryScalingChart
end Release061

end

end OAI
