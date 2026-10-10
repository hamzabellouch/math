import Mathlib
import OAI.Geometry.HyperbolicGroups.MappedPicture
import OAI.Geometry.HyperbolicGroups.PictureUnderlyingGraph
import OAI.Geometry.HyperbolicGroups.PlanarSubpairing
import OAI.Geometry.HyperbolicGroups.SubpairingGraph

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch.PictureMap
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*}
variable (M : PictureMap D)

/-- Retain all literal edge copies whose endpoints are adjacent in T.
Fixed darts are stubs; no parallel edge is silently identified. -/
def graphPairing (T : SimpleGraph M.GraphVertex) : Perm D :=
  Function.Involutive.toPerm (fun x => if T.Adj (M.vertexClass x) (M.vertexClass (M.edge x))
    then M.edge x else x) (by
    intro x
    by_cases h : T.Adj (M.vertexClass x) (M.vertexClass (M.edge x))
    · simp only [ite_eq_left h,M.edge_edge,ite_eq_left h.symm]
    · simp only [ite_eq_right h])

lemma graphPairing_apply (T : SimpleGraph M.GraphVertex) (x : D) :
    M.graphPairing T x = if T.Adj (M.vertexClass x) (M.vertexClass (M.edge x))
      then M.edge x else x := rfl

lemma graphPairing_sub (T : SimpleGraph M.GraphVertex) (x : D) :
    M.graphPairing T x = x ∨ M.graphPairing T x = M.edge x := by
  rw [M.graphPairing_apply]; split_ifs <;> simp

lemma graphPairing_graph (T : SimpleGraph M.GraphVertex) (hle : T ≤ M.underlyingGraph) :
    M.subpairingGraph (M.graphPairing T) (M.subpairing_sq _ (M.graphPairing_sub T)) = T := by
  ext v w
  constructor
  · rintro ⟨hne,x,rfl,rfl⟩
    rw [M.graphPairing_apply] at hne ⊢
    split_ifs at hne ⊢ with h
    · exact h
    · exact (hne rfl).elim
  · intro h
    obtain ⟨hne,x,hx,hy⟩ := hle h
    refine ⟨hne,x,hx,?_⟩
    rw [M.graphPairing_apply,ite_eq_left (by rwa [hx,hy])]
    exact hy

lemma subpairing_span_of_connected (q : Perm D) (hq : q*q = 1)
    (hc : (M.subpairingGraph q hq).Connected) :
    SameCycle.setoid M.vertex ⊔ SameCycle.setoid q = ⊤ := by
  let s := SameCycle.setoid M.vertex ⊔ SameCycle.setoid q
  let f : M.GraphVertex → Quotient s := Quotient.map id (show SameCycle.setoid M.vertex ≤ s from le_sup_left)
  have hadj : ∀ {v w}, (M.subpairingGraph q hq).Adj v w → f v = f w := by
    rintro v w ⟨_,x,rfl,rfl⟩
    exact Quotient.sound ((show SameCycle.setoid q ≤ s from le_sup_right) (SameCycle.rfl.apply_right (f := q)))
  have hpath : ∀ {v w}, (M.subpairingGraph q hq).Walk v w → f v = f w := by
    intro v w p
    induction p with
    | nil => rfl
    | cons h p ih => exact (hadj h).trans ih
  apply top_unique
  intro x y _
  obtain ⟨p⟩ := hc (M.vertexClass x) (M.vertexClass y)
  exact Quotient.exact (hpath p)

end HyperbolicObstruction.PictureSwitch.PictureMap
end
end

section

end
end

end OAI
