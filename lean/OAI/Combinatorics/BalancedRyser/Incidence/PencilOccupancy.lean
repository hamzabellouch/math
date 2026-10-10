import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

namespace OAI

namespace Balanced
open scoped _root_.Balanced

open Finset

variable {P I J : Type*} [DecidableEq P]

theorem card_le_exceptional_add_cover_budget
    (S E : Finset P) (B : Finset J) (G : J → Finset P) (k : ℕ)
    (hcover : S ⊆ E ∪ B.biUnion G)
    (htrace : ∀ j ∈ B, (G j ∩ S).card ≤ k) :
    S.card ≤ E.card + k * B.card := by
  have hsub : S ⊆ E ∪ B.biUnion (fun j => G j ∩ S) := by
    intro x hx
    rcases Finset.mem_union.mp (hcover hx) with he | hg
    · exact Finset.mem_union_left _ he
    · obtain ⟨j, hj, hxj⟩ := Finset.mem_biUnion.mp hg
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨j, hj, Finset.mem_inter.mpr ⟨hxj, hx⟩⟩)
  calc
    S.card ≤ (E ∪ B.biUnion (fun j => G j ∩ S)).card := Finset.card_le_card hsub
    _ ≤ E.card + (B.biUnion (fun j => G j ∩ S)).card := Finset.card_union_le _ _
    _ ≤ E.card + B.card * k := Nat.add_le_add_left
      (Finset.card_biUnion_le_card_mul B (fun j => G j ∩ S) k htrace) _
    _ = E.card + k * B.card := by rw [Nat.mul_comm]

theorem pencil_cover_card_bound
    (S E : Finset P) (A : Finset I) (F : I → Finset P)
    (B : Finset J) (G : J → Finset P) (k : ℕ)
    (hcover : S ⊆ A.biUnion F ∪ B.biUnion G)
    (hpencil : ∀ i ∈ A, F i ∩ S ⊆ E)
    (htrace : ∀ j ∈ B, (G j ∩ S).card ≤ k) :
    S.card ≤ E.card + k * B.card := by
  apply card_le_exceptional_add_cover_budget S E B G k _ htrace
  intro x hx
  rcases Finset.mem_union.mp (hcover hx) with hf | hg
  · obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp hf
    exact Finset.mem_union_left _ (hpencil i hi (Finset.mem_inter.mpr ⟨hxi, hx⟩))
  · exact Finset.mem_union_right _ hg

theorem affine_pencil_cover_card_bound
    (S : Finset P) (p : P) (A : Finset I) (F : I → Finset P)
    (B : Finset J) (G : J → Finset P)
    (hcover : S ⊆ A.biUnion F ∪ B.biUnion G)
    (hpencil : ∀ i ∈ A, F i ∩ S ⊆ {p})
    (htrace : ∀ j ∈ B, (G j ∩ S).card ≤ 1) :
    S.card ≤ 1 + B.card := by
  simpa using pencil_cover_card_bound S {p} A F B G 1 hcover hpencil htrace

theorem parallel_pencil_cover_card_bound
    (S : Finset P) (A : Finset I) (F : I → Finset P)
    (B : Finset J) (G : J → Finset P)
    (hcover : S ⊆ A.biUnion F ∪ B.biUnion G)
    (hpencil : ∀ i ∈ A, Disjoint (F i) S)
    (htrace : ∀ j ∈ B, (G j ∩ S).card ≤ 1) :
    S.card ≤ B.card := by
  have hsmall : ∀ i ∈ A, F i ∩ S ⊆ ∅ := by
    intro i hi
    rw [Finset.disjoint_iff_inter_eq_empty.mp (hpencil i hi)]
  simpa using pencil_cover_card_bound S ∅ A F B G 1 hcover hsmall htrace

end Balanced

end OAI
