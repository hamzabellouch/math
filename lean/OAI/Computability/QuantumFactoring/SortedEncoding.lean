import Mathlib
import OAI.Computability.QuantumFactoring.SortedWords

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic.SortedWords

def numbers {w : ℕ} (xs : List (Basis w)) : List ℕ := xs.map (fun a=>(bitsValue a).toNat)

lemma zero_number (w : ℕ) : (bitsValue (fun _ : Fin w=>false)).toNat=0 := by
  have hz : bitsValue (fun _ : Fin w=>false)=(0 : BitVec w) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [bitsValue_bit _ ⟨i,hi⟩]
    simp
  rw [hz]
  rfl
lemma numbers_pad {w : ℕ} (xs : List (Basis w)) (k : ℕ) :
    numbers (xs++List.replicate k (fun _=>false))=numbers xs++List.replicate k 0 := by
  simp only [numbers,List.map_append,List.map_replicate,zero_number]

/-- Literal compare-exchange sorting gives the exact source sorted padded
encoding, not just an arbitrary prime multiset. -/
theorem sort_correct {w N r : ℕ} (xs : List (Basis w))
    (hp : ∀ p∈numbers xs,p.Prime) (hprod : (numbers xs).prod=N) (hlen : xs.length ≤ r) :
    CorrectEncoding N r (numbers (sort (xs++List.replicate (r-xs.length) (fun _=>false)))) := by
  let zs := xs++List.replicate (r-xs.length) (fun _ : Fin w=>false)
  have hlen' : (numbers (sort zs)).length=r := by
    simp only [numbers,List.length_map,sort_length,zs,List.length_append,List.length_replicate]
    omega
  apply (factorListValid_iff hlen').mp
  have hperm : (numbers (sort zs)).Perm (numbers zs) := (sort_perm zs).map _
  refine ⟨?_,?_,?_⟩
  · intro p hpm
    have hz := hperm.mem_iff.mp hpm
    simp only [zs,numbers_pad] at hz
    rcases List.mem_append.mp hz with hx | hx
    · exact Or.inr (hp p hx)
    · exact Or.inl (List.mem_replicate.mp hx).2
  · exact List.pairwise_map.mpr (sort_sorted zs)
  · calc
      unpadProduct (numbers (sort zs))=unpadProduct (numbers zs) := (hperm.map _).prod_eq
      _ = N := by
        simp only [zs,numbers_pad]
        rw [unpadProduct_append _ _ (fun p hp'=> (hp p hp').ne_zero),hprod]

end ExactQuantumFactoring.BitArithmetic.SortedWords


end

end OAI
