import Mathlib
import OAI.Analysis.SymmetricDomains.CompactPeakRatio

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
open Set

def chartSubsetHomeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : OpenPartialHomeomorph X Y) (S : Set X) (hS : S ⊆ e.source) : S ≃ₜ e '' S where
  toFun x := ⟨e x,mem_image_of_mem e x.property⟩
  invFun y := ⟨e.symm y,by
    obtain ⟨x,hx,hxy⟩ := y.property
    rw [← hxy,e.left_inv (hS hx)]
    exact hx⟩
  left_inv x := Subtype.ext (e.left_inv (hS x.property))
  right_inv y := by
    apply Subtype.ext
    apply e.right_inv
    obtain ⟨x,hx,hxy⟩ := y.property
    rw [← hxy]
    exact e.map_source (hS hx)
  continuous_toFun := (e.continuousOn.mono hS).domRestrict.subtype_mk _
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply ContinuousOn.domRestrict
    apply e.symm.continuousOn.mono
    rintro _ ⟨x,hx,rfl⟩
    exact e.map_source (hS hx)

@[simp] lemma chartSubsetHomeomorph_apply
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : OpenPartialHomeomorph X Y) (S : Set X) (hS : S ⊆ e.source) (x : S) :
    (chartSubsetHomeomorph e S hS x : Y) = e x := rfl

@[simp] lemma chartSubsetHomeomorph_symm_apply
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : OpenPartialHomeomorph X Y) (S : Set X) (hS : S ⊆ e.source) (y : e '' S) :
    ((chartSubsetHomeomorph e S hS).symm y : X) = e.symm y := rfl

def Biholomorph.ofOpenPartialHomeomorph {n m : ℕ}
    (e : OpenPartialHomeomorph (Affine n) (Affine m))
    (ha : AnalyticOnNhd ℂ e e.source) (hai : AnalyticOnNhd ℂ e.symm e.target)
    (S : Set (Affine n)) (hS : S ⊆ e.source) : Biholomorph S (e '' S) where
  toHomeomorph := chartSubsetHomeomorph e S hS
  holomorphic_toFun := by
    intro p
    exact ⟨e.source,e.open_source,hS p.property,e,ha,fun _ _ => rfl⟩
  holomorphic_invFun := by
    intro p
    have hp : (p : Affine m) ∈ e.target := by
      obtain ⟨x,hx,hxp⟩ := p.property
      rw [← hxp]
      exact e.map_source (hS hx)
    exact ⟨e.target,e.open_target,hp,e.symm,hai,fun _ _ => rfl⟩

def affineProductCoordinates (m k : ℕ) : (Affine m × Affine k) ≃L[ℂ] Affine (m+k) :=
  ((LinearEquiv.sumArrowLequivProdArrow (Fin m) (Fin k) ℂ ℂ).symm.trans
    (LinearEquiv.piCongrLeft ℂ (fun _ : Fin (m+k) => ℂ) finSumFinEquiv)).toContinuousLinearEquiv

end Release061

end

end OAI
