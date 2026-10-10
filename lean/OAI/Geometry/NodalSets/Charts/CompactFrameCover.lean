import Mathlib.Topology.Compactness.LocallyCompact
import OAI.Geometry.NodalSets.Charts.LocalFrameTriple

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped Topology
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
variable {T : Type*} [TopologicalSpace T]

structure CompactFrameCover
    (g H : T → Coord →L[ℝ] Coord →L[ℝ] ℝ) (p : T → Coord) where
  indices : Finset T
  patch : T → Set T
  compact_patch : ∀ i, IsCompact (patch i)
  covers : ∀ t, ∃ i ∈ indices, t ∈ patch i
  data : ∀ i, AdmissibleFrameTriple (fun t : patch i ↦ g t)
    (fun t : patch i ↦ H t) (fun t : patch i ↦ p t)

namespace CompactFrameCover
variable {g H : T → Coord →L[ℝ] Coord →L[ℝ] ℝ} {p : T → Coord}
variable (d : CompactFrameCover g H p)
def Parameter := Σ i : d.indices, d.patch i
instance : TopologicalSpace d.Parameter := inferInstanceAs (TopologicalSpace (Σ i : d.indices, d.patch i))
instance : CompactSpace d.Parameter := by
  let (i : d.indices) : CompactSpace (d.patch i) := isCompact_iff_compactSpace.mp (d.compact_patch i)
  exact inferInstanceAs (CompactSpace (Σ i : d.indices, d.patch i))
def center (t : d.Parameter) : T := t.2.val
lemma continuous_center : Continuous d.center := by
  apply continuous_sigma
  intro i
  exact continuous_subtype_val
lemma surjective_center : Function.Surjective d.center := by
  intro t
  obtain ⟨i,hi,ht⟩ := d.covers t
  exact ⟨⟨⟨i,hi⟩,⟨t,ht⟩⟩,rfl⟩

def triple : AdmissibleFrameTriple (g ∘ d.center) (H ∘ d.center) (p ∘ d.center) where
  q t := (d.data t.1).q t.2
  continuous_q := continuous_sigma (fun i ↦ (d.data i).continuous_q)
  independent t := (d.data t.1).independent t.2
  perpendicular t := (d.data t.1).perpendicular t.2
  length t := (d.data t.1).length t.2
  strict t := (d.data t.1).strict t.2
  e t := (d.data t.1).e t.2
  continuous_e j k := continuous_sigma (fun i ↦ (d.data i).continuous_e j k)
  orthonormal t := (d.data t.1).orthonormal t.2
  first t := (d.data t.1).first t.2
  second t := (d.data t.1).second t.2
end CompactFrameCover

theorem exists_compact_frame_cover [CompactSpace T] [T2Space T]
    (g H : T → Coord →L[ℝ] Coord →L[ℝ] ℝ) (hg : Continuous g) (hH : Continuous H)
    (hs : ∀ t u v, g t u v = g t v u)
    (hpos : ∀ t v, v ≠ 0 → 0 < g t v v)
    (p : T → Coord) (hp : Continuous p) (hp0 : ∀ t, p t ≠ 0)
    (hdir : ∀ t, ∃ v : Coord, g t (p t) v = 0 ∧ g t v v = 1 ∧
      0 < H t (p t) (p t)+(g t (p t) (p t)+4)*H t v v) :
    Nonempty (CompactFrameCover g H p) := by
  classical
  have hex (t : T) := exists_local_frame_triple g H hg hH hs hpos p hp hp0 t (hdir t)
  choose U hU hd using hex
  choose K hK hKU hKc using fun t ↦ local_compact_nhds (hU t)
  have hcover : (univ : Set T) ⊆ ⋃ t, interior (K t) := by
    intro t _
    exact mem_iUnion.mpr ⟨t,mem_interior_iff_mem_nhds.mpr (hK t)⟩
  obtain ⟨s,hscover⟩ := isCompact_univ.elim_finite_subcover
    (fun t ↦ interior (K t)) (fun _ ↦ isOpen_interior) hcover
  refine ⟨⟨s,K,hKc,?_,?_⟩⟩
  · intro t
    obtain ⟨i,hi,ht⟩ := mem_iUnion₂.mp (hscover (mem_univ t))
    exact ⟨i,hi,interior_subset ht⟩
  · intro i
    exact (Classical.choice (hd i)).pullback
      (fun t : K i ↦ (⟨t,hKU i t.property⟩ : U i))
      (continuous_subtype_val.subtype_mk _)

end
end Yau.Geometry

end OAI
