import Mathlib
import OAI.RepresentationTheory.PartialPermutation.StandardTableaux

namespace OAI

section
namespace PartialPermutation
namespace Tableau
noncomputable section
open Finset

section Interleave
variable {α : Type*} [Fintype α] [PartialOrder α]

omit [PartialOrder α] in
lemma interleaving_compl_card (P : α → Prop) [DecidablePred P]
    (s : {s : Finset (Fin (Fintype.card α)) // s.card=Fintype.card {a // P a}}) :
    s.1ᶜ.card = Fintype.card {a // ¬P a} := by
  rw [Finset.card_compl, Fintype.card_fin, s.2, Fintype.card_subtype_compl]

def interleavingEnumeration (P : α → Prop) [DecidablePred P]
    (T : StandardFilling {a // P a}) (U : StandardFilling {a // ¬P a})
    (s : {s : Finset (Fin (Fintype.card α)) // s.card=Fintype.card {a // P a}}) :
    α ≃ Fin (Fintype.card α) :=
  (Equiv.sumCompl P).symm.trans ((Equiv.sumCongr T.1 U.1).trans
    (finSumEquivOfFinset s.2 (interleaving_compl_card P s)))

lemma interleavingEnumeration_pos (P : α → Prop) [DecidablePred P]
    (T : StandardFilling {a // P a}) (U : StandardFilling {a // ¬P a})
    (s : {s : Finset (Fin (Fintype.card α)) // s.card=Fintype.card {a // P a}})
    (a : α) (ha : P a) :
    interleavingEnumeration P T U s a = s.1.orderEmbOfFin s.2 (T.1 ⟨a,ha⟩) := by
  simp [interleavingEnumeration, Equiv.sumCompl_symm_apply_of_pos ha]

lemma interleavingEnumeration_neg (P : α → Prop) [DecidablePred P]
    (T : StandardFilling {a // P a}) (U : StandardFilling {a // ¬P a})
    (s : {s : Finset (Fin (Fintype.card α)) // s.card=Fintype.card {a // P a}})
    (a : α) (ha : ¬P a) :
    interleavingEnumeration P T U s a = s.1ᶜ.orderEmbOfFin
      (interleaving_compl_card P s) (U.1 ⟨a,ha⟩) := by
  simp [interleavingEnumeration, Equiv.sumCompl_symm_apply_of_neg ha]

def interleaveFilling (P : α → Prop) [DecidablePred P]
    (hP : ∀ a b, a < b → (P a ↔ P b))
    (T : StandardFilling {a // P a}) (U : StandardFilling {a // ¬P a})
    (s : {s : Finset (Fin (Fintype.card α)) // s.card=Fintype.card {a // P a}}) :
    StandardFilling α := by
  refine ⟨interleavingEnumeration P T U s, ?_⟩
  intro a b hab
  by_cases ha : P a
  · have hb := (hP a b hab).mp ha
    rw [interleavingEnumeration_pos P T U s a ha, interleavingEnumeration_pos P T U s b hb]
    exact (s.1.orderEmbOfFin s.2).strictMono (T.2 hab)
  · have hb : ¬P b := fun hp => ha ((hP a b hab).mpr hp)
    rw [interleavingEnumeration_neg P T U s a ha, interleavingEnumeration_neg P T U s b hb]
    exact (s.1ᶜ.orderEmbOfFin _).strictMono (U.2 hab)

lemma interleaveFilling_injective (P : α → Prop) [DecidablePred P]
    (hP : ∀ a b, a < b → (P a ↔ P b))
    (T : StandardFilling {a // P a}) (U : StandardFilling {a // ¬P a}) :
    Function.Injective (interleaveFilling P hP T U) := by
  intro s t hst
  have hval := congrArg Subtype.val hst
  have hsr : Set.range (fun a : {a // P a} => interleavingEnumeration P T U s a.1) = s.1 := by
    have heq : (fun a : {a // P a} => interleavingEnumeration P T U s a.1) =
        (s.1.orderEmbOfFin s.2) ∘ T.1 := by
      funext a
      exact interleavingEnumeration_pos P T U s a.1 a.2
    rw [heq, Set.range_comp, Equiv.range_eq_univ, Set.image_univ, Finset.range_orderEmbOfFin]
  have htr : Set.range (fun a : {a // P a} => interleavingEnumeration P T U t a.1) = t.1 := by
    have heq : (fun a : {a // P a} => interleavingEnumeration P T U t a.1) =
        (t.1.orderEmbOfFin t.2) ∘ T.1 := by
      funext a
      exact interleavingEnumeration_pos P T U t a.1 a.2
    rw [heq, Set.range_comp, Equiv.range_eq_univ, Set.image_univ, Finset.range_orderEmbOfFin]
  apply Subtype.ext
  apply Finset.coe_injective
  rw [← hsr, ← htr]
  congr 1
  funext a
  exact Equiv.congr_fun hval a.1

lemma interleaving_binomial_lower_bound (P : α → Prop) [DecidablePred P]
    (hP : ∀ a b, a < b → (P a ↔ P b)) :
    (Fintype.card α).choose (Fintype.card {a // P a}) ≤
      Fintype.card (StandardFilling α) := by
  have h := Fintype.card_le_of_injective
    (interleaveFilling P hP (chosenFilling _) (chosenFilling _))
    (interleaveFilling_injective P hP (chosenFilling _) (chosenFilling _))
  simpa only [Fintype.card_finset_len, Fintype.card_fin] using h
end Interleave

end
end Tableau
end PartialPermutation
end

end OAI
