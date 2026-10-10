import Mathlib

namespace OAI

noncomputable section
namespace Ostmann.Characters.HigherBiasSource
open Finset
attribute [local instance] Classical.propDecidable

def boundedCellLists (S : Finset ℤ) : ℕ → Finset (List ℤ)
  | 0 => {[]}
  | N+1 => insert [] ((S ×ˢ boundedCellLists S N).image (fun p => p.1 :: p.2))

@[simp] theorem mem_boundedCellLists (S : Finset ℤ) (N : ℕ) (l : List ℤ) :
    l ∈ boundedCellLists S N ↔ l.length ≤ N ∧ ∀ x ∈ l, x ∈ S := by
  induction N generalizing l with
  | zero => cases l <;> simp [boundedCellLists]
  | succ N ih =>
    cases l with
    | nil => simp [boundedCellLists]
    | cons a l =>
      simp only [boundedCellLists,mem_insert,mem_image,mem_product,List.cons_ne_nil,false_or,
        Prod.exists,List.cons.injEq,List.length_cons,
        Nat.succ_le_succ_iff,List.mem_cons,forall_eq_or_imp,ih]
      constructor
      · rintro ⟨_,_,⟨ha,hlen,hmem⟩,rfl,rfl⟩
        exact ⟨hlen,ha,hmem⟩
      · rintro ⟨hlen,ha,hmem⟩
        exact ⟨a,l,⟨ha,hlen,hmem⟩,rfl,rfl⟩

theorem boundedCellLists_card_add_one (S : Finset ℤ) (hS : 2 ≤ S.card) (N : ℕ) :
    (boundedCellLists S N).card+1 ≤ S.card^(N+1) := by
  induction N with
  | zero => simpa [boundedCellLists] using hS
  | succ N ih =>
    have hh := card_insert_le [] ((S ×ˢ boundedCellLists S N).image (fun p => p.1 :: p.2))
    have hi := card_image_le (s := S ×ˢ boundedCellLists S N) (f := fun p => p.1 :: p.2)
    rw [card_product] at hi
    have hm := Nat.mul_le_mul_left S.card ih
    rw [boundedCellLists,pow_succ]
    nlinarith

def configurationAlphabet (M : ℕ) : Finset ℤ := Icc (-(M:ℤ)-1) ((M:ℤ)+1)

@[simp] theorem configurationAlphabet_card (M : ℕ) :
    (configurationAlphabet M).card = 2*M+3 := by
  simp only [configurationAlphabet,Int.card_Icc]
  omega

@[simp] theorem mem_configurationAlphabet (M : ℕ) (h : ℤ) :
    h ∈ configurationAlphabet M ↔ |h| ≤ (M:ℤ)+1 := by
  simp only [configurationAlphabet,mem_Icc,abs_le]
  omega

end Ostmann.Characters.HigherBiasSource

end

end OAI
