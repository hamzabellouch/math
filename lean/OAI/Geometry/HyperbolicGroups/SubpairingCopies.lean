import Mathlib
import OAI.Geometry.HyperbolicGroups.PictureContact
import OAI.Geometry.HyperbolicGroups.SubpairingTree

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch.PictureMap
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D] [Fintype D] [Nonempty D]
variable (M : PictureMap D) (q : Perm D) (hq : ∀ x, q x = x ∨ q x = M.edge x)

abbrev RetainedContact := M.Contact (fun _ => True) (fun x => q x ≠ x)

def retainedContactEdge (a : M.RetainedContact q) : Sym2 M.GraphVertex :=
  s(M.vertexClass a.val, M.vertexClass (M.edge a.val))

include hq in
omit [DecidableEq D] [Fintype D] [Nonempty D] in
lemma retained_raw_edge (x : D) : q (M.edge x) ≠ M.edge x ↔ q x ≠ x := by
  rw [M.subpairing_edge q hq]
  exact not_congr M.edge.injective.eq_iff

include hq in
omit [Nonempty D] in
lemma retained_contact_card : q.support.card = 2 * Fintype.card (M.RetainedContact q) := by
  have hh := M.internal_card (fun _ => True) (fun x => q x ≠ x)
    (M.retained_raw_edge q hq)
  have he : q.support.card = Fintype.card {x : D // q x ≠ x} := by
    simpa only [mem_support] using (Fintype.card_coe q.support).symm
  rw [he]
  simpa only [← Nat.card_eq_fintype_card,InternalSide,and_true] using hh

include hq in
omit [DecidableEq D] [Nonempty D] in
lemma retained_contact_covers (x : D) (hx : q x ≠ x) :
    ∃ a : M.RetainedContact q, a.val = x ∨ a.val = M.edge x := by
  by_cases hn : M.number x < M.number (M.edge x)
  · exact ⟨⟨x,hx,trivial,trivial,hn⟩,Or.inl rfl⟩
  · refine ⟨⟨M.edge x,(M.retained_raw_edge q hq x).mpr hx,trivial,trivial,?_⟩,Or.inr rfl⟩
    rw [M.edge_edge]
    exact lt_of_le_of_ne (le_of_not_gt hn) (M.number_ne x).symm

omit [Nonempty D] in
lemma subpairing_edges_subset_retained :
    (M.subpairingGraph q (M.subpairing_sq q hq)).edgeFinset ⊆
      Finset.univ.image (M.retainedContactEdge q) := by
  intro e he
  induction e using Sym2.inductionOn with
  | hf v w =>
    have hadj : (M.subpairingGraph q (M.subpairing_sq q hq)).Adj v w := by simpa using he
    obtain ⟨hne,x,rfl,rfl⟩ := hadj
    have hx : q x ≠ x := fun hh => hne (congrArg M.vertexClass hh.symm)
    have hxe : q x = M.edge x := (hq x).resolve_left hx
    obtain ⟨a,ha | ha⟩ := M.retained_contact_covers q hq x hx
    · exact Finset.mem_image.mpr ⟨a,Finset.mem_univ _,by simp [retainedContactEdge,ha,hxe]⟩
    · exact Finset.mem_image.mpr ⟨a,Finset.mem_univ _,by
        simp only [retainedContactEdge,ha,M.edge_edge,hxe]
        exact Sym2.eq_swap⟩

/-- A one-boundary spanning subpairing has exactly one retained contact for
each edge of its underlying tree. Euler and connectivity rule out BOTH
loops and parallel copies, rather than silently forgetting them. -/
theorem tree_retained_contacts_bijective (hG : M.GenusZero)
    (hspan : SameCycle.setoid M.vertex ⊔ SameCycle.setoid q = ⊤)
    (hboundary : cycles (M.vertex*q) = 1) :
    Function.Injective (M.retainedContactEdge q) ∧
    (M.subpairingGraph q (M.subpairing_sq q hq)).edgeFinset =
      Finset.univ.image (M.retainedContactEdge q) := by
  classical
  have heuler := M.subpairing_euler q hq hG
  rw [hspan,card_quotient_top_one,hboundary,cycles_eq_card_classes] at heuler
  change (Nat.card M.GraphVertex : ℤ) + 1 - (q.support.card : ℤ)/2 = 2 at heuler
  have hc := M.retained_contact_card q hq
  have hcZ : (q.support.card : ℤ) = 2*(Fintype.card (M.RetainedContact q) : ℤ) := by
    exact_mod_cast hc
  rw [hcZ] at heuler
  have hv : Fintype.card M.GraphVertex = Fintype.card (M.RetainedContact q) + 1 := by
    rw [Nat.card_eq_fintype_card] at heuler
    omega
  have hconn := M.subpairing_connected q (M.subpairing_sq q hq) hspan
  have hlo := hconn.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card,← SimpleGraph.edgeFinset_card] at hlo
  have hs := M.subpairing_edges_subset_retained q hq
  have hle := Finset.card_le_card hs
  have hi := Finset.card_image_le (s := Finset.univ) (f := M.retainedContactEdge q)
  rw [Finset.card_univ] at hi
  have heq : (M.subpairingGraph q (M.subpairing_sq q hq)).edgeFinset = Finset.univ.image (M.retainedContactEdge q) := by
    apply Finset.eq_of_subset_of_card_le hs
    omega
  refine ⟨?_,heq⟩
  have hic : (Finset.univ.image (M.retainedContactEdge q)).card =
      (Finset.univ : Finset (M.RetainedContact q)).card := by
    rw [Finset.card_univ]
    rw [← heq]
    omega
  have hinj := Finset.card_image_iff.mp hic
  exact fun a b hab => hinj (Finset.mem_univ a) (Finset.mem_univ b) hab

end HyperbolicObstruction.PictureSwitch.PictureMap
end
end

section

end
end

end OAI
