import Mathlib
import OAI.Geometry.HyperbolicGroups.BoundaryList

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D] [Fintype D]

lemma cycles_le_half_of_no_fixed (p : Perm D) (h : ∀ x, p x ≠ x) :
    2 * cycles p ≤ Fintype.card D := by
  have hb : ∀ s : Multiset ℕ, (∀ t ∈ s, 2 ≤ t) → 2*s.card ≤ s.sum := by
    intro s
    induction s using Multiset.induction_on with
    | empty => simp
    | @cons a s ih =>
      intro hs
      have ha := hs a (by simp)
      have hi := ih (fun t ht => hs t (by simp [ht]))
      simp only [Multiset.card_cons,Multiset.sum_cons]
      omega
  have hc := hb p.cycleType (fun _ hm => two_le_of_mem_cycleType hm)
  have hs : p.support = Finset.univ := by ext x; simp [mem_support,h x]
  rw [sum_cycleType,hs,Finset.card_univ] at hc
  simp only [cycles,defect,hs,Finset.card_univ]
  omega

lemma IsBoundary.cycles_eq_one {p : Perm D} {xs : List D}
    (h : IsBoundary p xs) (hall : ∀ x, x ∈ xs) (hne : xs ≠ []) : cycles p = 1 := by
  have hp : p = xs.formPerm := by ext x; exact h.turn x (hall x)
  have hf : xs.toFinset = Finset.univ := by ext x; simp [hall x]
  have hl : xs.length = Fintype.card D := by
    rw [← List.toFinset_card_of_nodup h.nodup,hf,Finset.card_univ]
  cases xs with
  | nil => exact False.elim (hne rfl)
  | cons a s =>
    rw [hp,cycles,defect_list a s h.nodup]
    simp only [List.length_cons] at hl
    omega

/-- A one-face genus-zero side pairing has a genuine valence-one vertex.
The genus assumption is essential: the analogous torus pairing has none. -/
theorem PictureMap.single_face_leaf (M : PictureMap D) (hG : M.GenusZero)
    {xs : List D} (hb : IsBoundary M.face xs) (hall : ∀ x, x ∈ xs)
    (hne : xs ≠ []) : ∃ x, M.face (M.edge x) = x := by
  have : Nonempty D := by
    cases xs with
    | nil => exact False.elim (hne rfl)
    | cons a xs => exact ⟨a⟩
  have : Nonempty (Quotient M.components) := ⟨Quotient.mk _ (Classical.choice ‹Nonempty D›)⟩
  have hco : 0 < Nat.card (Quotient M.components) := Nat.card_pos
  have hf := hb.cycles_eq_one hall hne
  by_contra hn
  push Not at hn
  have hv := cycles_le_half_of_no_fixed M.vertex hn
  change M.euler = _ at hG
  rw [PictureMap.euler,hf] at hG
  omega

end HyperbolicObstruction.PictureSwitch
end
end

section

end
end

end OAI
