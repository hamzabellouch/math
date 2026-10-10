import Mathlib
import OAI.Geometry.HyperbolicGroups.FinitePolyhedronLocal
import OAI.Geometry.HyperbolicGroups.FinitePolyhedronVoltage
import OAI.Geometry.HyperbolicGroups.PathInSet

namespace OAI

/-! Canonical straight paths and the actual contractible open vertex stars.
There are no combinatorial-to-topological equivalences assumed here. -/
noncomputable section

open scoped Topology
open Set
namespace HyperbolicObstruction.FinitePolyhedron
variable {V : Type*} [Fintype V] [DecidableEq V] (K : AbstractSimplicialComplex V)

lemma wideStar_vertex (v : V) : wideStar K (vertex K v) = {y | 0 < y v} := by
  ext y
  simp only [wideStar,vertex,mem_ofPred_eq,Pi.single_apply]
  constructor
  · intro h; simpa using h v (by simp)
  · intro h i hi
    by_cases hv : i = v
    · subst i; exact h
    · simp [hv] at hi

lemma openStar_ambient_starConvex (v : V) :
    StarConvex ℝ (vertex K v).val (carrierSet K ∩ {y | 0 < y v}) := by
  simpa only [wideStar_vertex] using wideStar_starConvex K (vertex K v)

omit [DecidableEq V] in
lemma vertex_mem_openStar (v : V) : vertex K v ∈ openStar K v := by
  simp [openStar,vertex]

def openStarHomeomorph (v : V) :
    openStar K v ≃ₜ ((carrierSet K ∩ {y : V → ℝ | 0 < y v}) : Set (V → ℝ)) where
  toFun x := ⟨x.val.val,x.val.property,x.property⟩
  invFun x := ⟨⟨x.val,x.property.1⟩,x.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

instance openStar_contractible (v : V) : ContractibleSpace (openStar K v) := by
  have : ContractibleSpace ((carrierSet K ∩ {y : V → ℝ | 0 < y v}) : Set (V → ℝ)) :=
    (openStar_ambient_starConvex K v).contractibleSpace
      ⟨(vertex K v).val,(vertex K v).property,vertex_mem_openStar K v⟩
  exact (openStarHomeomorph K v).contractibleSpace

/-- The affine path when its entire segment lies in the actual carrier. -/
def straight (x y : Carrier K) (h : segment ℝ x.val y.val ⊆ carrierSet K) : Path x y where
  toFun t := ⟨Path.segment x.val y.val t,h (Path.range_segment x.val y.val ▸ mem_range_self t)⟩
  continuous_toFun := (Path.segment x.val y.val).continuous.subtype_mk _
  source' := Subtype.ext (Path.segment x.val y.val).source
  target' := Subtype.ext (Path.segment x.val y.val).target

omit [DecidableEq V] in
@[simp] lemma straight_val (x y : Carrier K) (h) (t) :
    (straight K x y h t).val = AffineMap.lineMap x.val y.val (t : ℝ) := rfl

omit [DecidableEq V] in
lemma straight_in_face {s : Finset V} (hs : s ∈ K.faces) (x y : Carrier K)
    (hx : x.val ∈ simplex s) (hy : y.val ∈ simplex s) :
    segment ℝ x.val y.val ⊆ carrierSet K :=
  ((simplex_convex s).segment_subset hx hy).trans (simplex_subset_carrier K hs)

def facePath {s : Finset V} (hs : s ∈ K.faces) (x y : Carrier K)
    (hx : x.val ∈ simplex s) (hy : y.val ∈ simplex s) : Path x y :=
  straight K x y (straight_in_face K hs x y hx hy)

def edgePath {a b : V} (h : {a,b} ∈ K.faces) : Path (vertex K a) (vertex K b) :=
  facePath K h _ _ (vertex_mem_simplex K (by simp)) (vertex_mem_simplex K (by simp))

/-- The radial path from a star-center to a point in its open star. -/
def starPath (v : V) (x : Carrier K) (hx : x ∈ openStar K v) : Path (vertex K v) x :=
  straight K _ _ (((openStar_ambient_starConvex K v).segment_subset ⟨x.property,hx⟩).trans inter_subset_left)

lemma starPath_mem (v : V) (x : Carrier K) (hx : x ∈ openStar K v) (t) :
    starPath K v x hx t ∈ openStar K v :=
  ((openStar_ambient_starConvex K v).segment_subset ⟨x.property,hx⟩
    (Path.range_segment (vertex K v).val x.val ▸ mem_range_self t)).2

lemma homotopic_in_star (v : V) {x y : Carrier K} (p q : Path x y)
    (hp : ∀ t, p t ∈ openStar K v) (hq : ∀ t, q t ∈ openStar K v) : p.Homotopic q :=
  PathInSet.homotopic (openStar K v) p q hp hq

end HyperbolicObstruction.FinitePolyhedron
end

end OAI
