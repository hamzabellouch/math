import Mathlib
import OAI.Geometry.HyperbolicGroups.FinitePolyhedronPaths

namespace OAI

/-! Literal equality tests for barycentric edges. These prevent arbitrary
choices of edge homotopies from being silently identified at intersections. -/
noncomputable section

open scoped Topology unitInterval
namespace HyperbolicObstruction.FinitePolyhedron
variable {V : Type*} [Fintype V] [DecidableEq V] (K : AbstractSimplicialComplex V)

lemma vertex_injective : Function.Injective (vertex K) := by
  intro a b hab
  by_contra hn
  have hh := congrArg (fun x : Carrier K => x.val a) hab
  simp [vertex,hn] at hh

lemma edgePath_coordinate {a b : V} (h : {a,b} ∈ K.faces) (s : I) (j : V) :
    (edgePath K h s).val j = (if j = a then 1-(s:ℝ) else 0) + (if j = b then (s:ℝ) else 0) := by
  change (AffineMap.lineMap (vertex K a).val (vertex K b).val (s:ℝ)) j = _
  simp [AffineMap.lineMap_apply_module,vertex,Pi.single_apply]

lemma edgePath_eq_vertex_cases {a b c : V} (h : {a,b} ∈ K.faces) (hab : a ≠ b)
    (s : I) (he : edgePath K h s = vertex K c) :
    (s = 0 ∧ a = c) ∨ (s = 1 ∧ b = c) := by
  have hc : c = a ∨ c = b := by
    by_contra hn
    push Not at hn
    have hh := congrArg (fun x : Carrier K => x.val c) he
    change (edgePath K h s).val c = (vertex K c).val c at hh
    rw [edgePath_coordinate] at hh
    simp [vertex,hn.1,hn.2] at hh
  rcases hc with hc|hc
  all_goals subst c
  · left
    refine ⟨Subtype.ext ?_,rfl⟩
    have hh := congrArg (fun x : Carrier K => x.val b) he
    change (edgePath K h s).val b = (vertex K _).val b at hh
    rw [edgePath_coordinate] at hh
    simpa [vertex,Pi.single_apply,hab,Ne.symm hab] using hh
  · right
    refine ⟨Subtype.ext ?_,rfl⟩
    have hh := congrArg (fun x : Carrier K => x.val b) he
    change (edgePath K h s).val b = (vertex K _).val b at hh
    rw [edgePath_coordinate] at hh
    simpa [vertex,Pi.single_apply,hab,Ne.symm hab] using hh

lemma edgePath_eq_edge_interior {a b c d : V} (h : {a,b} ∈ K.faces) (h' : {c,d} ∈ K.faces)
    (hab : a ≠ b) (hcd : c ≠ d) (s t : I) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (he : edgePath K h s = edgePath K h' t) :
    (a = c ∧ b = d ∧ s = t) ∨ (a = d ∧ b = c ∧ s = unitInterval.symm t) := by
  have hspos : 0 < (s:ℝ) := lt_of_le_of_ne s.property.1 (fun hz => hs0 (Subtype.ext hz.symm))
  have hslt : (s:ℝ) < 1 := lt_of_le_of_ne s.property.2 (fun hz => hs1 (Subtype.ext hz))
  have ha : a = c ∨ a = d := by
    by_contra hn
    push Not at hn
    have hh := congrArg (fun x : Carrier K => x.val a) he
    simp [edgePath_coordinate,hn.1,hn.2,hab] at hh
    linarith
  have hb : b = c ∨ b = d := by
    by_contra hn
    push Not at hn
    have hh := congrArg (fun x : Carrier K => x.val b) he
    simp [edgePath_coordinate,hn.1,hn.2,Ne.symm hab] at hh
    exact hs0 hh
  rcases ha with rfl|rfl <;> rcases hb with hb|hb
  · exact (hab hb.symm).elim
  · subst d
    left
    refine ⟨rfl,rfl,Subtype.ext ?_⟩
    have hh := congrArg (fun x : Carrier K => x.val b) he
    simpa [edgePath_coordinate,Ne.symm hab] using hh
  · subst c
    right
    refine ⟨rfl,rfl,Subtype.ext ?_⟩
    have hh := congrArg (fun x : Carrier K => x.val b) he
    simpa [edgePath_coordinate,Ne.symm hab] using hh
  · exact (hab hb.symm).elim

end HyperbolicObstruction.FinitePolyhedron
end

end OAI
