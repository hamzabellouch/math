import Mathlib
import OAI.Computability.QuantumFactoring.OrderSamplerMass
import OAI.Computability.QuantumFactoring.SortedEncoding

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open OrderTrial SortedWords

def canonicalWords (n : ℕ) (xs : List ℕ) : List (Basis n) := xs.map (natBasis n)

lemma natBasis_number {n : ℕ} (a : Basis n) : natBasis n (bitsValue a).toNat=a := by
  apply (bitsEquiv n).injective
  apply BitVec.eq_of_toNat_eq
  change (bitsValue (natBasis n (bitsValue a).toNat)).toNat=(bitsValue a).toNat
  rw [natBasis_value,Nat.mod_eq_of_lt (bitsValue a).isLt]

lemma canonical_numbers {n : ℕ} (xs : List (Basis n)) : canonicalWords n (numbers xs)=xs := by
  simp only [canonicalWords,numbers,List.map_map,Function.comp_def,natBasis_number]
  exact List.map_id xs

lemma numbers_canonical {n : ℕ} (xs : List ℕ) (hb : ∀ a∈xs,a < 2^n) :
    numbers (canonicalWords n xs)=xs := by
  simp only [canonicalWords,numbers,List.map_map]
  calc
    _ = xs.map id := List.map_congr_left (fun a ha=>by
      simp only [Function.comp_apply,natBasis_value,Nat.mod_eq_of_lt (hb a ha),id_eq])
    _ = xs := List.map_id xs

lemma canonical_length (n : ℕ) (xs : List ℕ) : (canonicalWords n xs).length=xs.length := List.length_map (natBasis n)
lemma canonical_append (n : ℕ) (xs ys : List ℕ) :
    canonicalWords n (xs++ys)=canonicalWords n xs++canonicalWords n ys := List.map_append

end ExactQuantumFactoring.BitArithmetic


end

end OAI
