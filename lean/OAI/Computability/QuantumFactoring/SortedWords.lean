import Mathlib
import OAI.Computability.QuantumFactoring.BitEncoding
import OAI.Computability.QuantumFactoring.FactorEncoding

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
namespace SortedWords

def LEWord {w : ℕ} (a b : Basis w) : Prop := PaddedOrder (bitsValue a).toNat (bitsValue b).toNat
instance {w : ℕ} (a b : Basis w) : Decidable (LEWord a b) :=
  inferInstanceAs (Decidable (_=0 ∨ (_≠0 ∧ _ ≤ _)))

lemma le_total {w : ℕ} (a b : Basis w) : LEWord a b ∨ LEWord b a := by
  dsimp only [LEWord,PaddedOrder]
  omega
lemma le_trans {w : ℕ} {a b c : Basis w} (h : LEWord a b) (h' : LEWord b c) : LEWord a c := by
  dsimp only [LEWord,PaddedOrder] at *
  omega

def insert {w : ℕ} (a : Basis w) : List (Basis w)→List (Basis w)
  | []=>[a]
  | b::bs=>if LEWord a b then a::insert b bs else b::insert a bs

def sort {w : ℕ} : List (Basis w)→List (Basis w)
  | []=>[]
  | a::as=>insert a (sort as)

lemma insert_perm {w : ℕ} (a : Basis w) (bs : List (Basis w)) : (insert a bs).Perm (a::bs) := by
  induction bs generalizing a with
  | nil=>rfl
  | cons b bs ih=>
    rw [insert]
    split_ifs
    · exact (ih b).cons a
    · exact ((ih a).cons b).trans (List.Perm.swap b a bs).symm
lemma insert_length {w : ℕ} (a : Basis w) (bs : List (Basis w)) : (insert a bs).length=bs.length+1 :=
  (insert_perm a bs).length_eq
lemma sort_perm {w : ℕ} (bs : List (Basis w)) : (sort bs).Perm bs := by
  induction bs with
  | nil=>rfl
  | cons b bs ih=>exact (insert_perm b (sort bs)).trans (ih.cons b)
lemma sort_length {w : ℕ} (bs : List (Basis w)) : (sort bs).length=bs.length := (sort_perm bs).length_eq

lemma insert_sorted {w : ℕ} (a : Basis w) (bs : List (Basis w)) (hs : bs.Pairwise LEWord) :
    (insert a bs).Pairwise LEWord := by
  induction bs generalizing a with
  | nil=>simp [insert]
  | cons b bs ih=>
    obtain ⟨hfirst,htail⟩ := List.pairwise_cons.mp hs
    rw [insert]
    split_ifs with hab
    · rw [List.pairwise_cons]
      refine ⟨?_,ih b htail⟩
      intro c hc
      rcases List.mem_cons.mp ((insert_perm b bs).mem_iff.mp hc) with rfl | hc
      · exact hab
      · exact le_trans hab (hfirst c hc)
    · rw [List.pairwise_cons]
      refine ⟨?_,ih a htail⟩
      intro c hc
      rcases List.mem_cons.mp ((insert_perm a bs).mem_iff.mp hc) with rfl | hc
      · exact (le_total _ _).resolve_left hab
      · exact hfirst c hc
lemma sort_sorted {w : ℕ} (bs : List (Basis w)) : (sort bs).Pairwise LEWord := by
  induction bs with
  | nil=>simp [sort]
  | cons b bs ih=>exact insert_sorted b (sort bs) ih

end SortedWords
end ExactQuantumFactoring.BitArithmetic


end

end OAI
