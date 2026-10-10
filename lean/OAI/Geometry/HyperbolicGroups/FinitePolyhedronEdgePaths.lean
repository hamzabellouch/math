import Mathlib
import OAI.Geometry.HyperbolicGroups.FinitePolyhedronPaths

namespace OAI

/-! Edge paths generate the actual path homotopy groupoid of a finite
barycentric realization. The proof uses the literal open stars, not an
unproved simplicial-approximation principle. -/
noncomputable section

open Set
namespace HyperbolicObstruction.FinitePolyhedron
variable {V : Type*} [Fintype V] [DecidableEq V] (K : AbstractSimplicialComplex V)

abbrev inFace (s : Finset V) : Set (Carrier K) := {x | x.val ∈ simplex s}

def inFaceHomeomorph {s : Finset V} (hs : s ∈ K.faces) : inFace K s ≃ₜ simplex s where
  toFun x := ⟨x.val.val,x.property⟩
  invFun x := ⟨⟨x.val,simplex_subset_carrier K hs x.property⟩,x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

omit [DecidableEq V] in
lemma inFace_contractible {s : Finset V} (hs : s ∈ K.faces) : ContractibleSpace (inFace K s) := by
  obtain ⟨i,hi⟩ := (K.isRelLowerSet_faces hs).1
  have : Nonempty (simplex s) := ⟨⟨(vertex K i).val,vertex_mem_simplex K hi⟩⟩
  have : ContractibleSpace (simplex s) := (simplex_convex s).contractibleSpace ⟨(vertex K i).val,vertex_mem_simplex K hi⟩
  exact (inFaceHomeomorph K hs).contractibleSpace

omit [DecidableEq V] in
lemma homotopic_in_face {s : Finset V} (hs : s ∈ K.faces) {x y : Carrier K}
    (p q : Path x y) (hp : ∀ t, p t ∈ inFace K s) (hq : ∀ t, q t ∈ inFace K s) : p.Homotopic q := by
  have := inFace_contractible K hs
  exact PathInSet.homotopic (inFace K s) p q hp hq

omit [DecidableEq V] in
lemma straight_mem_face {s : Finset V} {x y : Carrier K} (h)
    (hx : x ∈ inFace K s) (hy : y ∈ inFace K s) (t) : straight K x y h t ∈ inFace K s :=
  (simplex_convex s).segment_subset hx hy
    (Path.range_segment x.val y.val ▸ mem_range_self t)

lemma positive_mem_face {s : Finset V} (x : Carrier K)
    (hx : x ∈ inFace K s) {a : V} (ha : x ∈ openStar K a) : a ∈ s := by
  by_contra hn
  have hp : 0 < x.val a := ha
  rw [hx.2.2 a hn] at hp
  exact lt_irrefl _ hp

lemma commonStar_edge (x : Carrier K) {a b : V}
    (ha : x ∈ openStar K a) (hb : x ∈ openStar K b) : {a,b} ∈ K.faces := by
  apply face_of_positive K x (by simp)
  intro i hi
  simp only [Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with rfl|rfl <;> assumption

lemma radial_bridge (x : Carrier K) {a b : V}
    (ha : x ∈ openStar K a) (hb : x ∈ openStar K b) :
    ((starPath K a x ha).trans (starPath K b x hb).symm).Homotopic
      (edgePath K (commonStar_edge K x ha hb)) := by
  obtain ⟨s,hs,hxs⟩ := x.property.2.2
  have hx : x ∈ inFace K s := ⟨x.property.1,x.property.2.1,hxs⟩
  have hsa := vertex_mem_simplex K (positive_mem_face K x hx ha)
  have hsb := vertex_mem_simplex K (positive_mem_face K x hx hb)
  apply homotopic_in_face K hs
  · intro t
    have ht := mem_range_self (f := (starPath K a x ha).trans (starPath K b x hb).symm) t
    rw [Path.trans_range] at ht
    rcases ht with ⟨u,heq⟩|⟨u,heq⟩
    · rw [←heq]; exact straight_mem_face K _ hsa hx u
    · rw [←heq]
      change starPath K b x hb (unitInterval.symm u) ∈ inFace K s
      exact straight_mem_face K _ hsb hx _
  · intro t
    unfold edgePath facePath
    exact straight_mem_face K _ hsa hsb t

/-- A genuine finite vertex edge path. -/
inductive EdgeChain : V → V → Type _
  | nil (a) : EdgeChain a a
  | cons {a b c} (edge : {a,b} ∈ K.faces) (tail : EdgeChain b c) : EdgeChain a c

end HyperbolicObstruction.FinitePolyhedron
end

end OAI
