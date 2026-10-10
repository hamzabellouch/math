import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.PolygonArea
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.PolygonGridComparison

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section PolygonTrackArea
open Classical Set MeasureTheory
namespace PolygonGrid

noncomputable def trackUnion {m : ℕ} (S : Fin m → Set (ℝ×ℝ)) : Set PlaneTracks :=
  ⋃i, {i.val} ×ˢ S i

@[simp] theorem mem_trackUnion {m : ℕ} (S : Fin m → Set (ℝ×ℝ)) (i : Fin m) (x : ℝ×ℝ) :
    (i.val,x)∈trackUnion S ↔ x∈S i := by
  constructor
  · intro h
    obtain ⟨j,hj,hx⟩ := Set.mem_iUnion.mp h
    have he : i=j := Fin.ext hj
    simpa only [←he] using hx
  · intro hx
    exact Set.mem_iUnion.mpr ⟨i,rfl,hx⟩

theorem trackUnion_mono {m : ℕ} {S T : Fin m → Set (ℝ×ℝ)} (h : ∀i,S i⊆T i) :
    trackUnion S⊆trackUnion T := by
  intro p hp
  obtain ⟨i,hi,hp⟩ := Set.mem_iUnion.mp hp
  exact Set.mem_iUnion.mpr ⟨i,hi,h i hp⟩

theorem trackUnion_region {m : ℕ} {S : Fin m → Set (ℝ×ℝ)}
    (h : ∀i,S i⊆PolygonArea.square) : trackUnion S⊆region m := by
  intro p hp
  obtain ⟨i,hi,hp⟩ := Set.mem_iUnion.mp hp
  exact ⟨hi ▸ i.isLt,h i hp⟩

@[simp] theorem volume_trackUnion {m : ℕ} (S : Fin m → Set (ℝ×ℝ))
    (hS : ∀i,MeasurableSet (S i)) : μ (trackUnion S)=∑i,volume (S i) := by
  have hdis : Pairwise (fun i j : Fin m => Disjoint ({i.val}×ˢ S i) ({j.val}×ˢ S j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro p ⟨hi,-⟩ ⟨hj,-⟩
    exact hij (Fin.ext (hi.symm.trans hj))
  rw [trackUnion,measure_iUnion hdis (fun i => (measurableSet_singleton _).prod (hS i))]
  simp only [μ,Measure.prod_prod,Measure.count_singleton,one_mul,tsum_fintype]
  rfl

theorem bank_representative {a m : ℕ} (U : Fin m → polygonAlgebra a) :
    ∃ S : Set PlaneTracks, S⊆region m ∧
      (∀i : Fin m,∀x : GenericSquare a,(i.val,x.val)∈S ↔ x∈(U i).val) ∧
      μ (closure S)=∑i,PolygonArea.area (U i) ∧
      μ (interior S)=∑i,PolygonArea.area (U i) := by
  choose R hR hm hn he using fun i => PolygonArea.representative (U i).property
  have hmR : ∀i,MeasurableSet (R i) := hm
  have harea (i : Fin m) : volume (R i)=PolygonArea.area (U i) :=
    (PolygonArea.area_eq_rep (U i) (hR i) (he i)).symm
  have hvol : μ (trackUnion R)=∑i,PolygonArea.area (U i) := by
    rw [volume_trackUnion R hmR]
    exact Finset.sum_congr rfl (fun i _ => harea i)
  have hclosure : closure (trackUnion R)⊆trackUnion (fun i => closure (R i)) := by
    apply (isClosed_iUnion_of_finite (fun i => isClosed_singleton.prod isClosed_closure)).closure_subset_iff.mpr
    exact trackUnion_mono (fun _ => subset_closure)
  have hinterior : trackUnion (fun i => interior (R i))⊆interior (trackUnion R) := by
    apply interior_maximal (trackUnion_mono (fun _ => interior_subset))
    exact isOpen_iUnion (fun i => (isOpen_discrete _).prod isOpen_interior)
  have hvclosure : μ (trackUnion (fun i => closure (R i)))=∑i,PolygonArea.area (U i) := by
    rw [volume_trackUnion _ (fun _ => isClosed_closure.measurableSet)]
    apply Finset.sum_congr rfl
    intro i _
    rw [measure_congr (PolygonArea.closure_ae_eq (hn i)),harea]
  have hvinterior : μ (trackUnion (fun i => interior (R i)))=∑i,PolygonArea.area (U i) := by
    rw [volume_trackUnion _ (fun _ => isOpen_interior.measurableSet)]
    apply Finset.sum_congr rfl
    intro i _
    rw [measure_congr (PolygonArea.interior_ae_eq (hn i)),harea]
  refine ⟨trackUnion R,trackUnion_region hR,?_,?_,?_⟩
  · intro i x
    exact (mem_trackUnion R i x.val).trans (he i x).symm
  · exact le_antisymm ((measure_mono hclosure).trans_eq hvclosure)
      (hvol.symm.trans_le (measure_mono subset_closure))
  · exact le_antisymm ((measure_mono interior_subset).trans_eq hvol)
      (hvinterior.symm.trans_le (measure_mono hinterior))

theorem polygon_grid_comparison {a m : ℕ} (U V : Fin m → polygonAlgebra a)
    (h : (∑i,PolygonArea.area (U i)) < ∑i,PolygonArea.area (V i)) :
    ∃ (S T : Set PlaneTracks) (δ : ℝ), 0 < δ ∧
      (∀i : Fin m,∀x : GenericSquare a,(i.val,x.val)∈S ↔ x∈(U i).val) ∧
      (∀i : Fin m,∀x : GenericSquare a,(i.val,x.val)∈T ↔ x∈(V i).val) ∧
      ∀ε : ℝ, 0 < ε → ε < δ →
        ∃ (N : ℕ) (I J : Finset (Index m N)), Nonempty (I ↪ J) ∧
          S⊆⋃i∈I,cell ε i ∧ ∀j∈J,cell ε j⊆T := by
  obtain ⟨S,hS,heS,hcS,hiS⟩ := bank_representative U
  obtain ⟨T,hT,heT,hcT,hiT⟩ := bank_representative V
  have hh : μ (closure S)<μ (interior T) := by rwa [hcS,hiT]
  obtain ⟨δ,hδ,hmatch⟩ := strict_grid_comparison hS hT hh
  exact ⟨S,T,δ,hδ,heS,heT,hmatch⟩

end PolygonGrid
end PolygonTrackArea

end SimpleAmenable
end
end

end OAI
