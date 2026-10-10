import Mathlib
import OAI.Geometry.HyperbolicGroups.PlanarEdgeOrdering

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D] [Fintype D]

lemma joins_pairing (p q : Perm D) (l : List (D × D)) (hl : swaps l = q)
    (hpairs : ∀ ab ∈ l, q ab.1 = ab.2) :
    joins (SameCycle.setoid p) l = SameCycle.setoid p ⊔ SameCycle.setoid q := by
  apply le_antisymm
  · apply joins_le _ _ _ le_sup_left
    intro ab hab
    apply (show SameCycle.setoid q ≤ SameCycle.setoid p ⊔ SameCycle.setoid q from le_sup_right)
    rw [← hpairs ab hab]; exact SameCycle.rfl.apply_right
  · apply sup_le (le_joins _ _)
    have h₁ : SameCycle.setoid (1 : Perm D) ≤ SameCycle.setoid p := by
      intro a b hab; exact (hab.eq_of_left rfl).sameCycle p
    have h := sameCycle_joins h₁ l
    simpa only [one_mul,hl] using h

namespace PictureMap
variable (M : PictureMap D) (q : Perm D)
variable (hsub : ∀ x, q x = x ∨ q x = M.edge x)
include hsub

omit [DecidableEq D] [Fintype D] in
lemma subpairing_edge (x : D) : q (M.edge x) = M.edge (q x) := by
  rcases hsub x with hx | hx
  · rw [hx]
    rcases hsub (M.edge x) with he | he
    · exact he
    · rw [M.edge_edge] at he
      have hh := q.injective (he.trans hx.symm)
      exact False.elim (M.edge_ne x hh)
  · rw [hx,M.edge_edge]
    rcases hsub (M.edge x) with he | he
    · have hh := q.injective (hx.trans he.symm)
      exact False.elim ((M.edge_ne x) hh.symm)
    · simpa only [M.edge_edge] using he

omit [DecidableEq D] [Fintype D] in
lemma subpairing_sq : q * q = 1 := by
  ext x
  change q (q x) = x
  rcases hsub x with hx | hx
  · rw [hx,hx]
  · rw [hx,M.subpairing_edge q hsub x,hx,M.edge_edge]

omit [DecidableEq D] [Fintype D] in
lemma complement_subpairing (x : D) : (q * M.edge) x = x ∨ (q * M.edge) x = M.edge x := by
  rw [mul_apply,M.subpairing_edge q hsub x]
  rcases hsub x with hx | hx
  · exact Or.inr (congrArg M.edge hx)
  · exact Or.inl ((congrArg M.edge hx).trans (M.edge_edge x))

lemma complement_support : (q * M.edge).support = Finset.univ \ q.support := by
  ext x
  simp only [mem_support,Finset.mem_sdiff,Finset.mem_univ,true_and,not_not]
  rw [mul_apply,M.subpairing_edge q hsub x]
  rcases hsub x with hx | hx
  · rw [hx]; exact ⟨fun _ => rfl,fun _ => M.edge_ne x⟩
  · rw [hx,M.edge_edge]
    simp only [ne_eq,not_true_eq_false]
    exact iff_of_false (fun h => h) (M.edge_ne x)

/-- Literal edge-subgraph planarity with retained vertex slots. Fixed points
of q are unpaired stubs, so support/2 counts ONLY remaining edges. This
Euler equation is proved for EVERY chosen subset of actual edges, and is the
subgraph input needed in a recursive planar separator construction. -/
theorem subpairing_euler (hG : M.GenusZero) :
    cycles M.vertex + cycles (M.vertex * q) - (q.support.card : ℤ) / 2 =
      2 * (Nat.card (Quotient (SameCycle.setoid M.vertex ⊔ SameCycle.setoid q)) : ℤ) := by
  obtain ⟨l,hl,hn,hpairs⟩ := involution_pairs q (M.subpairing_sq q hsub)
  let r := q * M.edge
  have hrsub := M.complement_subpairing q hsub
  obtain ⟨t,ht,htn,htpairs⟩ := involution_pairs r (M.subpairing_sq r hrsub)
  have hsupp : q.support.card + r.support.card = Fintype.card D := by
    rw [show r.support = Finset.univ \ q.support from M.complement_support q hsub]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ]
    have hh := Finset.card_le_card (Finset.subset_univ q.support)
    rw [Finset.card_univ] at hh
    omega
  have hprod : swaps (l ++ t) = M.edge := by
    rw [swaps_append,show swaps l = q from hl,show swaps t = r from ht]
    change q * (q * M.edge) = M.edge
    rw [← mul_assoc,M.subpairing_sq q hsub,one_mul]
  have hlen : 2 * (l ++ t).length = Fintype.card D := by
    rw [List.length_append]; omega
  have hact : ∀ ab ∈ l ++ t, M.edge ab.1 = ab.2 := by
    intro ab hab
    rcases List.mem_append.mp hab with hab | hab
    · obtain ⟨hne,he⟩ := hpairs ab hab
      rcases hsub ab.1 with hx | hx
      · exact False.elim (hne (hx.symm.trans he))
      · exact hx.symm.trans he
    · obtain ⟨hne,he⟩ := htpairs ab hab
      rcases hrsub ab.1 with hx | hx
      · exact False.elim (hne (hx.symm.trans he))
      · exact hx.symm.trans he
  have hfull := M.paired_potential_eq hG (l ++ t) hprod hlen hact
  have hp := potential_prefix_eq (p := M.vertex) (s := SameCycle.setoid M.vertex) le_rfl l t hfull
  rw [joins_pairing M.vertex q l hl (fun ab hab => (hpairs ab hab).2),
    show swaps l = q from hl,← cycles_eq_card_classes] at hp
  omega

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

section

end
end

end OAI
