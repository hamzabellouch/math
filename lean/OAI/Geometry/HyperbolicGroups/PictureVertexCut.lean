import Mathlib
import OAI.Geometry.HyperbolicGroups.RelativePartition
import OAI.Geometry.HyperbolicGroups.PictureUnderlyingGraph

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D I : Type*} [DecidableEq D] [Fintype D] [Fintype I]
namespace PictureMap
variable (M : PictureMap D)

omit [DecidableEq D] in
lemma incident_darts_card (S : Finset M.GraphVertex) :
    Nat.card {x : D // M.vertexClass x ∈ S} =
      ∑ v : S, Nat.card {x : D // M.vertexClass x = v.val} := by
  let e : {x : D // M.vertexClass x ∈ S} ≃
      (v : S) × {x : D // M.vertexClass x = v.val} := {
    toFun := fun x => ⟨⟨M.vertexClass x.val,x.property⟩,x.val,rfl⟩
    invFun := fun x => ⟨x.2.val,by rw [x.2.property]; exact x.1.property⟩
    left_inv := fun _ => rfl
    right_inv := by rintro ⟨⟨v,hv⟩,x,hx⟩; cases hx; rfl }
  rw [Nat.card_congr e]
  simp only [Nat.card_eq_fintype_card,Fintype.card_sigma]

omit [DecidableEq D] [Fintype I] in
/-- Recover the true multigraph cut count from a vertex separator in the
underlying simple graph. Every unordered edge copy is retained; multiple
contacts inject into distinct incident darts of separator vertices. -/
theorem relative_cuts_le_separator (active : D → Prop) (part : M.GraphVertex → I)
    (S : Finset M.GraphVertex) (d : ℕ)
    (hdegree : ∀ v ∈ S, Nat.card {x : D // M.vertexClass x = v} ≤ d)
    (hhit : ∀ x, active x → active (M.edge x) →
      part (M.vertexClass x) ≠ part (M.vertexClass (M.edge x)) →
      M.vertexClass x ∈ S ∨ M.vertexClass (M.edge x) ∈ S) :
    Fintype.card (RelativeCutContact M active (part ∘ M.vertexClass)) ≤ d * S.card := by
  let f : RelativeCutContact M active (part ∘ M.vertexClass) →
      {x : D // M.vertexClass x ∈ S} := fun x =>
    if h : M.vertexClass x.val ∈ S then ⟨x.val,h⟩ else
      ⟨M.edge x.val,(hhit x.val x.property.1 x.property.2.1 x.property.2.2.1).resolve_left h⟩
  have hf : Function.Injective f := by
    intro x y heq
    have he := congrArg Subtype.val heq
    apply Subtype.ext
    dsimp only [f] at he
    split_ifs at he with hx hy hy
    · exact he
    · have hxlt := x.property.2.2.2
      have hylt := y.property.2.2.2
      change x.val = M.edge y.val at he
      have hh : M.number (M.edge y.val) < M.number y.val := by
        simpa only [he,M.edge_edge] using hxlt
      exact (lt_asymm hylt hh).elim
    · have hxlt := x.property.2.2.2
      have hylt := y.property.2.2.2
      change M.edge x.val = y.val at he
      have hh : M.number (M.edge x.val) < M.number x.val := by
        simpa only [← he,M.edge_edge] using hylt
      exact (lt_asymm hxlt hh).elim
    · exact M.edge.injective he
  have h1 := Nat.card_le_card_of_injective f hf
  have h2 : Nat.card {x : D // M.vertexClass x ∈ S} ≤ d * S.card := by
    rw [M.incident_darts_card]
    calc
      _ ≤ ∑ _v : S, d := Finset.sum_le_sum (fun v _ => hdegree v.val v.property)
      _ = d * S.card := by simp [mul_comm]
  simpa only [Nat.card_eq_fintype_card] using h1.trans h2

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

section

end
end

end OAI
