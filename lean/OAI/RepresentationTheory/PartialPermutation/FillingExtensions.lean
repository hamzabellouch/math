import Mathlib
import OAI.RepresentationTheory.PartialPermutation.StandardTableaux

namespace OAI

section
namespace PartialPermutation
namespace Tableau
noncomputable section
open Finset

section Extension
variable {α β : Type*} [Fintype α] [PartialOrder α] [Fintype β] [PartialOrder β]

def fillingCongr (e : α ≃o β) : StandardFilling α ≃ StandardFilling β where
  toFun T := ⟨e.symm.toEquiv.trans (T.1.trans (finCongr (Fintype.card_congr e.toEquiv))),
    (Fin.cast_strictMono (Fintype.card_congr e.toEquiv)).comp (T.2.comp e.symm.strictMono)⟩
  invFun T := ⟨e.toEquiv.trans (T.1.trans (finCongr (Fintype.card_congr e.symm.toEquiv))),
    (Fin.cast_strictMono (Fintype.card_congr e.symm.toEquiv)).comp (T.2.comp e.strictMono)⟩
  left_inv T := by apply Subtype.ext; apply Equiv.ext; intro a; apply Fin.ext; simp
  right_inv T := by apply Subtype.ext; apply Equiv.ext; intro a; apply Fin.ext; simp

omit [PartialOrder α] in
lemma sum_subtype_card (P : α → Prop) [DecidablePred P] :
    Fintype.card {a // P a} + Fintype.card {a // ¬P a} = Fintype.card α := by
  simpa only [Fintype.card_sum] using Fintype.card_congr (Equiv.sumCompl P)

def concatEnumeration (P : α → Prop) [DecidablePred P]
    (T : StandardFilling {a // P a}) (U : StandardFilling {a // ¬P a}) :
    α ≃ Fin (Fintype.card α) :=
  (Equiv.sumCompl P).symm.trans ((Equiv.sumCongr T.1 U.1).trans
    (finSumFinEquiv.trans (finCongr (sum_subtype_card P))))

lemma concatEnumeration_pos (P : α → Prop) [DecidablePred P]
    (T : StandardFilling {a // P a}) (U : StandardFilling {a // ¬P a})
    (a : α) (ha : P a) : (concatEnumeration P T U a).val = (T.1 ⟨a,ha⟩).val := by
  simp [concatEnumeration, Equiv.sumCompl_symm_apply_of_pos ha]

lemma concatEnumeration_neg (P : α → Prop) [DecidablePred P]
    (T : StandardFilling {a // P a}) (U : StandardFilling {a // ¬P a})
    (a : α) (ha : ¬P a) : (concatEnumeration P T U a).val =
      Fintype.card {a // P a} + (U.1 ⟨a,ha⟩).val := by
  simp [concatEnumeration, Equiv.sumCompl_symm_apply_of_neg ha]

def extendFilling (P : α → Prop) [DecidablePred P] (hP : IsLowerSet {a | P a})
    (T : StandardFilling {a // P a}) (U : StandardFilling {a // ¬P a}) :
    StandardFilling α := by
  refine ⟨concatEnumeration P T U, ?_⟩
  intro a b hab
  change (concatEnumeration P T U a).val < (concatEnumeration P T U b).val
  by_cases ha : P a <;> by_cases hb : P b
  · rw [concatEnumeration_pos P T U a ha, concatEnumeration_pos P T U b hb]
    exact T.2 (show (⟨a,ha⟩ : {a // P a}) < ⟨b,hb⟩ from hab)
  · rw [concatEnumeration_pos P T U a ha, concatEnumeration_neg P T U b hb]
    have h := (T.1 ⟨a,ha⟩).isLt
    omega
  · exact (ha (hP hab.le hb)).elim
  · rw [concatEnumeration_neg P T U a ha, concatEnumeration_neg P T U b hb]
    exact Nat.add_lt_add_left (U.2 (show (⟨a,ha⟩ : {a // ¬P a}) < ⟨b,hb⟩ from hab)) _

lemma filling_count_mono_lowerSet (P : α → Prop) [DecidablePred P]
    (hP : IsLowerSet {a | P a}) :
    Fintype.card (StandardFilling {a // P a}) ≤ Fintype.card (StandardFilling α) := by
  let U := chosenFilling {a // ¬P a}
  apply Fintype.card_le_of_injective (fun T => extendFilling P hP T U)
  intro T S he
  apply Subtype.ext
  apply Equiv.ext
  intro a
  apply Fin.ext
  have h := congrArg (fun T : StandardFilling α => (T.1 a.1).val) he
  change (concatEnumeration P T U a.1).val = (concatEnumeration P S U a.1).val at h
  simpa only [concatEnumeration_pos P _ _ _ a.2] using h

lemma filling_count_mono_complement (P : α → Prop) [DecidablePred P]
    (hP : IsLowerSet {a | P a}) :
    Fintype.card (StandardFilling {a // ¬P a}) ≤ Fintype.card (StandardFilling α) := by
  let T := chosenFilling {a // P a}
  apply Fintype.card_le_of_injective (fun U => extendFilling P hP T U)
  intro U V he
  apply Subtype.ext
  apply Equiv.ext
  intro a
  apply Fin.ext
  have h := congrArg (fun S : StandardFilling α => (S.1 a.1).val) he
  change (concatEnumeration P T U a.1).val = (concatEnumeration P T V a.1).val at h
  simp only [concatEnumeration_neg P _ _ _ a.2] at h
  exact Nat.add_left_cancel h

end Extension

def subdiagramCellsEquiv {μ ν : YoungDiagram} (h : μ ≤ ν) :
    μ.cells ≃o {x : ν.cells // x.1 ∈ μ.cells} where
  toFun x := ⟨⟨x.1,h x.2⟩,x.2⟩
  invFun x := ⟨x.1.1,x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

lemma standardCount_mono {μ ν : YoungDiagram} (h : μ ≤ ν) :
    standardCount μ ≤ standardCount ν := by
  classical
  have hh : IsLowerSet {x : ν.cells | x.1 ∈ μ.cells} := by
    intro x y hxy hy
    exact μ.isLowerSet hxy hy
  have hcard := Fintype.card_congr (fillingCongr (subdiagramCellsEquiv h))
  unfold standardCount
  rw [hcard]
  exact filling_count_mono_lowerSet _ hh

end
end Tableau
end PartialPermutation
end

end OAI
