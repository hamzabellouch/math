import Mathlib
import OAI.Geometry.HyperbolicGroups.FinitePolyhedronMonodromy

namespace OAI

/-! Closed simplices in the actual voltage cover. The extended chart formula is
continuous even when its anchor coordinate is zero, by the triangle cocycle. -/
noncomputable section

open scoped Topology
open Set
namespace HyperbolicObstruction.FinitePolyhedron.Voltage
variable {V : Type*} [Fintype V] [DecidableEq V]
  {K : AbstractSimplicialComplex V} {G : Type*} [Group G]
  [TopologicalSpace G] [DiscreteTopology G] (v : Voltage K G)

instance totalSpace_t2 : T2Space v.TotalSpace := by
  apply t2Space_iff_disjoint_nhds.mpr
  intro e f hne
  by_cases hp : v.proj e = v.proj f
  · let j := v.core.indexAt e.proj
    let t := v.core.localTriv j
    have he : e ∈ t.source := t.mem_source.mpr (v.core.mem_baseSet_at e.proj)
    have hf : f ∈ t.source := t.mem_source.mpr (by
      change v.proj f ∈ openStar K j
      rw [←hp]
      exact v.core.mem_baseSet_at e.proj)
    have hn : t e ≠ t f := fun h => hne (t.injOn he hf h)
    exact (t.continuousAt he).disjoint (disjoint_nhds_nhds.mpr hn) (t.continuousAt hf)
  · exact v.core.continuous_proj.continuousAt.disjoint
      (disjoint_nhds_nhds.mpr hp) v.core.continuous_proj.continuousAt

def closedFace (s : Finset V) : Set (Carrier K) := {x | x.val ∈ simplex s}
omit [DecidableEq V] in
lemma closedFace_isClosed (s : Finset V) : IsClosed (closedFace (K := K) s) :=
  (simplex_closed s).preimage continuous_subtype_val
instance closedFace_compact (s : Finset V) : CompactSpace (closedFace (K := K) s) :=
  isCompact_iff_compactSpace.mp (closedFace_isClosed s).isCompact

lemma member_of_positive {s : Finset V} (x : closedFace (K := K) s) {a : V}
    (ha : 0 < x.val.val a) : a ∈ s := by
  by_contra hn
  have hz := x.property.2.2 a hn
  exact (ne_of_gt ha) hz

lemma inChart_change_face {s : Finset V} (hs : s ∈ K.faces)
    {a b : V} (ha : a ∈ s) (hb : b ∈ s) (x : closedFace (K := K) s) (g : G) :
    v.inChart b x.val (g * v.value a b) = v.inChart a x.val g := by
  apply v.totalSpace_ext
  · rfl
  simp only [inChart_coordinate,mul_assoc]
  congr 1
  apply v.triangle
  apply (K.isRelLowerSet_faces hs).2 _ (by simp)
  intro z hz
  simp only [Finset.mem_insert,Finset.mem_singleton] at hz
  rcases hz with rfl|rfl|rfl
  · exact ha
  · exact hb
  · exact member_of_positive x (v.core.mem_baseSet_at x.val)

lemma inChart_continuous_face {s : Finset V} (hs : s ∈ K.faces)
    {a : V} (ha : a ∈ s) (g : G) :
    Continuous (fun x : closedFace (K := K) s => v.inChart a x.val g) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  let j := v.core.indexAt x.val
  have hx : x.val ∈ openStar K j := v.core.mem_baseSet_at x.val
  have hj : j ∈ s := member_of_positive x hx
  have he : (fun z : closedFace (K := K) s => v.inChart a z.val g) =
      fun z => v.inChart j z.val (g * v.value a j) := by
    funext z
    exact (v.inChart_change_face hs ha hj z g).symm
  rw [he]
  apply ((v.core.localTriv j).toOpenPartialHomeomorph.continuousAt_symm ?_).comp
    (continuousAt_subtype_val.prodMk continuousAt_const)
  exact (v.core.localTriv j).mem_target.mpr hx

def faceLift {s : Finset V} (hs : s ∈ K.faces) {a : V} (ha : a ∈ s) (g : G) :
    C(closedFace (K := K) s,v.TotalSpace) :=
  ⟨fun x => v.inChart a x.val g,v.inChart_continuous_face hs ha g⟩

@[simp] lemma faceLift_proj {s : Finset V} (hs : s ∈ K.faces) {a : V}
    (ha : a ∈ s) (g : G) (x : closedFace (K := K) s) :
    v.proj (v.faceLift hs ha g x) = x.val := rfl

lemma faceLift_injective {s : Finset V} (hs : s ∈ K.faces) {a : V}
    (ha : a ∈ s) (g : G) : Function.Injective (v.faceLift hs ha g) := by
  intro x y h
  exact Subtype.ext (congrArg v.proj h)

lemma faceLift_closedEmbedding {s : Finset V} (hs : s ∈ K.faces) {a : V}
    (ha : a ∈ s) (g : G) : Topology.IsClosedEmbedding (v.faceLift hs ha g) :=
  (v.faceLift hs ha g).continuous.isClosedEmbedding (v.faceLift_injective hs ha g)

lemma faceLift_chart {s : Finset V} (hs : s ∈ K.faces) {a b : V}
    (ha : a ∈ s) (hb : b ∈ s) (g : G) (x : closedFace (K := K) s) :
    v.core.localTriv b (v.faceLift hs ha g x) = (x.val,g * v.value a b) := by
  apply Prod.ext
  · rfl
  change (g * v.value a (v.core.indexAt x.val)) * v.value (v.core.indexAt x.val) b = _
  rw [mul_assoc]
  congr 1
  apply v.triangle
  apply (K.isRelLowerSet_faces hs).2 _ (by simp)
  intro z hz
  simp only [Finset.mem_insert,Finset.mem_singleton] at hz
  rcases hz with rfl|rfl|rfl
  · exact ha
  · exact member_of_positive x (v.core.mem_baseSet_at x.val)
  · exact hb

/-- Anchor is finite data; no choice of deck coordinate is lost. -/
abbrev FaceAnchor := {sa : Finset V × V // sa.1 ∈ K.faces ∧ sa.2 ∈ sa.1}

def liftedClosedFace (q : FaceAnchor (K := K) × G) : Set v.TotalSpace :=
  Set.range (v.faceLift q.1.property.1 q.1.property.2 q.2)

lemma liftedClosedFace_closed (q : FaceAnchor (K := K) × G) :
    IsClosed (v.liftedClosedFace q) :=
  (v.faceLift_closedEmbedding q.1.property.1 q.1.property.2 q.2).isClosed_range

lemma liftedClosedFace_cover : ⋃ q, v.liftedClosedFace q = Set.univ := by
  apply Set.eq_univ_of_forall
  intro e
  obtain ⟨s,hs,hx⟩ := e.proj.property.2.2
  have hxs : e.proj ∈ closedFace s := ⟨e.proj.property.1,e.proj.property.2.1,hx⟩
  let a := v.core.indexAt e.proj
  have ha : a ∈ s := member_of_positive ⟨e.proj,hxs⟩ (v.core.mem_baseSet_at e.proj)
  apply Set.mem_iUnion.mpr
  refine ⟨(⟨(s,a),hs,ha⟩,v.coordinate e),⟨e.proj,hxs⟩,?_⟩
  apply v.totalSpace_ext
  · rfl
  change v.coordinate e * v.value a a = v.coordinate e
  rw [v.self,mul_one]

/-- The original covering topology has a locally finite closed simplex cover.
There are only finitely many base faces/anchors and at most one deck label per
anchored face in a fixed small chart neighborhood. -/
lemma liftedClosedFace_locallyFinite : LocallyFinite v.liftedClosedFace := by
  intro e
  let j := v.core.indexAt e.proj
  let t := v.core.localTriv j
  have he : e ∈ t.source := t.mem_source.mpr (v.core.mem_baseSet_at e.proj)
  let U : Set v.TotalSpace := t.source ∩ (fun z => (t z).2) ⁻¹' {(t e).2}
  have hopen : IsOpen U := t.continuousOn.snd.isOpen_inter_preimage t.open_source (isOpen_discrete _)
  refine ⟨U,hopen.mem_nhds ⟨he,rfl⟩,?_⟩
  apply Set.Finite.of_injOn (f := Prod.fst) (t := Set.univ) (fun _ _ => Set.mem_univ _) ?_
    (Set.toFinite _)
  rintro ⟨q,g⟩ hq ⟨q',g'⟩ hq' hqq
  change q = q' at hqq
  subst q'
  obtain ⟨x,⟨z,rfl⟩,hx⟩ := hq
  obtain ⟨x',⟨z',rfl⟩,hx'⟩ := hq'
  have hj : j ∈ q.val.1 := member_of_positive z (t.mem_source.mp hx.1)
  have h1 := congrArg Prod.snd (v.faceLift_chart q.property.1 q.property.2 hj g z)
  have h2 := congrArg Prod.snd (v.faceLift_chart q.property.1 q.property.2 hj g' z')
  have hx0 : (t (v.faceLift q.property.1 q.property.2 g z)).2 = (t e).2 := hx.2
  have hx1 : (t (v.faceLift q.property.1 q.property.2 g' z')).2 = (t e).2 := hx'.2
  apply Prod.ext
  · rfl
  exact mul_right_cancel (h1.symm.trans (hx0.trans (hx1.symm.trans h2)))

end HyperbolicObstruction.FinitePolyhedron.Voltage
end

end OAI
