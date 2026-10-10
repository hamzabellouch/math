import Mathlib
import OAI.Geometry.HyperbolicGroups.PictureMap
import OAI.Geometry.HyperbolicGroups.PermEuler
import OAI.Geometry.HyperbolicGroups.PictureUnderlyingGraph
import OAI.Geometry.HyperbolicGroups.PictureCotreeColor

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch.PictureMap
open Equiv Equiv.Perm PlanarRecursion
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D] [Fintype D]
variable (M : PictureMap D)

def vertexRepresentative (v : M.GraphVertex) : D := Quotient.out v
omit [DecidableEq D] [Fintype D] in
lemma vertexClass_representative (v : M.GraphVertex) :
    M.vertexClass (M.vertexRepresentative v) = v := Quotient.out_eq v

def vertexColor {C : Type*} (color : D → C) (v : M.GraphVertex) : C :=
  color (M.vertexRepresentative v)

omit [DecidableEq D]

/-- Outside a set containing every edge-color boundary, incident face
colors agree around the ENTIRE literal vertex rotation orbit. -/
lemma color_eq_on_vertex_outside {C : Type*} (color : D → C)
    (hface : ∀ x, color (M.face x) = color x) (S : Set M.GraphVertex)
    (hboundary : ∀ x, color (M.edge x) ≠ color x → M.vertexClass x ∈ S)
    (x y : D) (hv : M.vertexClass x = M.vertexClass y) (hx : M.vertexClass x ∉ S) :
    color x = color y := by
  classical
  let f : D → Option C := fun z => if M.vertexClass z ∈ S then none else some (color z)
  have hf : ∀ z, f (M.vertex z) = f z := by
    intro z
    simp only [f,M.vertexClass_vertex]
    by_cases hz : M.vertexClass z ∈ S
    · rw [ite_eq_left hz,ite_eq_left hz]
    · rw [ite_eq_right hz,ite_eq_right hz]
      congr 1
      have he : color (M.edge z) = color z := by
        by_contra hh
        exact hz (hboundary z hh)
      exact (hface (M.edge z)).trans he
  have he : f x = f y := (sameCycle_le_of_apply (s := Setoid.ker f)
    (fun z => (hf z).symm)) ((M.vertexClass_eq_iff _ _).mp hv)
  have hy : M.vertexClass y ∉ S := hv ▸ hx
  simp only [f,ite_eq_right hx,ite_eq_right hy,Option.some.injEq] at he
  exact he

lemma vertexColor_eq_dart_outside {C : Type*} (color : D → C)
    (hface : ∀ x, color (M.face x) = color x) (S : Set M.GraphVertex)
    (hboundary : ∀ x, color (M.edge x) ≠ color x → M.vertexClass x ∈ S)
    (x : D) (hx : M.vertexClass x ∉ S) :
    M.vertexColor color (M.vertexClass x) = color x := by
  apply M.color_eq_on_vertex_outside color hface S hboundary
  · exact M.vertexClass_representative _
  · rwa [M.vertexClass_representative]

lemma vertexColor_adj_outside {C : Type*} (color : D → C)
    (hface : ∀ x, color (M.face x) = color x) (S : Set M.GraphVertex)
    (hboundary : ∀ x, color (M.edge x) ≠ color x → M.vertexClass x ∈ S)
    {v w : M.GraphVertex} (hadj : M.underlyingGraph.Adj v w) (hv : v ∉ S) (hw : w ∉ S) :
    M.vertexColor color v = M.vertexColor color w := by
  obtain ⟨hne,x,rfl,rfl⟩ := hadj
  rw [M.vertexColor_eq_dart_outside color hface S hboundary _ hv,
    M.vertexColor_eq_dart_outside color hface S hboundary _ hw]
  by_contra he
  exact hv (hboundary x (fun hh => he hh.symm))

/-- A connected set of primal vertices off the rooted separator carries
one deleted-dual-component color. This closes the actual separation bridge
from rotation-system boundaries to the underlying graph. -/
theorem vertexColor_connected_outside {C : Type*} (color : D → C)
    (hface : ∀ x, color (M.face x) = color x) (S : Set M.GraphVertex)
    (hboundary : ∀ x, color (M.edge x) ≠ color x → M.vertexClass x ∈ S)
    (U : Set M.GraphVertex) (hU : ∀ v ∈ U, v ∉ S)
    (hconn : (M.underlyingGraph.induce U).Preconnected) :
    ∀ v ∈ U, ∀ w ∈ U, M.vertexColor color v = M.vertexColor color w := by
  have hpath : ∀ {a b : U}, (M.underlyingGraph.induce U).Walk a b →
      M.vertexColor color a.val = M.vertexColor color b.val := by
    intro a b p
    induction p with
    | nil => rfl
    | @cons a b c h p ih =>
      exact (M.vertexColor_adj_outside color hface S hboundary h
        (hU a.val a.property) (hU b.val b.property)).trans ih
  intro v hv w hw
  obtain ⟨p⟩ := hconn ⟨v,hv⟩ ⟨w,hw⟩
  exact hpath p

end HyperbolicObstruction.PictureSwitch.PictureMap
end
end

section

end
end

end OAI
