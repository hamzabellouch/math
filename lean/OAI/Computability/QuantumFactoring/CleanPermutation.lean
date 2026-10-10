import Mathlib
import OAI.Computability.QuantumFactoring.OracleLayout

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BooleanNetwork

lemma packed_single_swap {n r : ℕ} (x y : Basis n) (j : Fin n) :
    packed r x y ∘ Equiv.swap (⟨j.val,by omega⟩ : Fin (n+n+r)) ⟨n+j.val,by omega⟩ =
      packed r (Function.update x j (y j)) (Function.update y j (x j)) := by
  funext i
  by_cases ha : i.val = j.val
  · have hi : i = (⟨j.val,by omega⟩ : Fin (n+n+r)) := Fin.ext ha
    simp only [hi]
    rw [Function.comp_apply, Equiv.swap_apply_left, packed_target]
    simp [packed, j.isLt]
  · by_cases hb : i.val = n+j.val
    · have hi : i = (⟨n+j.val,by omega⟩ : Fin (n+n+r)) := Fin.ext hb
      simp only [hi]
      rw [Function.comp_apply, Equiv.swap_apply_right, packed_input]
      simp [packed, j.isLt]
    · rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne
        (by intro h; exact ha (congrArg Fin.val h))
        (by intro h; exact hb (congrArg Fin.val h))]
      unfold packed
      split_ifs with hn hnn
      · rw [Function.update_of_ne]
        intro h; exact ha (congrArg Fin.val h)
      · rw [Function.update_of_ne]
        intro h
        have hh := congrArg Fin.val h
        dsimp at hh
        omega
      · rfl

def swapPrefix (n r : ℕ) : (k : ℕ) → k ≤ n → List (Instruction (n+n+r))
  | 0, _ => []
  | k+1, h => swapPrefix n r k (by omega) ++
      swapAt ⟨k,by omega⟩ ⟨n+k,by omega⟩ (by intro he; have hh := congrArg Fin.val he; dsimp at hh; omega)

lemma swapPrefix_length (n r k : ℕ) (hk : k ≤ n) :
    (swapPrefix n r k hk).length = 3*k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [swapPrefix, swapAt, ih (by omega)]; omega

lemma swapPrefix_basis {n r : ℕ} (x y : Basis n) (k : ℕ) (hk : k ≤ n) :
    (programMatrix (swapPrefix n r k hk)).mulVec (basisVector (packed r x y)) =
      basisVector (packed r (fun i => if i.val<k then y i else x i)
        (fun i => if i.val<k then x i else y i)) := by
  induction k with
  | zero => simp [swapPrefix, programMatrix_nil]
  | succ k ih =>
    rw [swapPrefix, programMatrix_append, ← Matrix.mulVec_mulVec, ih (by omega),
      swapAt_basis, packed_single_swap _ _ (⟨k,by omega⟩ : Fin n)]
    congr 1
    congr 1 <;> funext i
    all_goals
      by_cases hi : i.val=k
      · have he : i = (⟨k,by omega⟩ : Fin n) := Fin.ext hi
        simp only [he]
        simp
      · rw [Function.update_of_ne (by intro he; exact hi (congrArg Fin.val he))]
        have he : (i.val < k+1) ↔ i.val<k := by omega
        simp only [he]

lemma swapBlocks_basis {n r : ℕ} (x y : Basis n) :
    (programMatrix (swapPrefix n r n le_rfl)).mulVec (basisVector (packed r x y)) =
      basisVector (packed r y x) := by
  rw [swapPrefix_basis]
  congr 1
  congr 1 <;> funext i <;> simp [i.isLt]

/-- The standard clean implementation of a bijection uses a verified forward
and inverse Boolean network, two work registers, and only the named gates. -/
def cleanPermutation {n r : ℕ} (f g : BooleanNetwork n n)
    (hf : f.net.count ≤ r) (hg : g.net.count ≤ r) : List (Instruction (n+n+r)) :=
  oracleOn f hf ++ swapPrefix n r n le_rfl ++ oracleOn g hg

lemma cleanPermutation_basis {n r : ℕ} (f g : BooleanNetwork n n)
    (hf : f.net.count ≤ r) (hg : g.net.count ≤ r) (x : Basis n)
    (hfg : g.eval (f.eval x) = x) :
    (programMatrix (cleanPermutation f g hf hg)).mulVec
        (basisVector (packed r x (fun _ => false))) =
      basisVector (packed r (f.eval x) (fun _ => false)) := by
  rw [cleanPermutation, programMatrix_append, programMatrix_append,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, oracleOn_basis]
  simp only [Bool.false_xor]
  rw [swapBlocks_basis, oracleOn_basis, hfg]
  simp

lemma cleanPermutation_length {n r : ℕ} (f g : BooleanNetwork n n)
    (hf : f.net.count ≤ r) (hg : g.net.count ≤ r) :
    (cleanPermutation f g hf hg).length ≤ 4*f.net.count+4*g.net.count+7*n := by
  have h₁ := oracleOn_length f hf
  have h₂ := oracleOn_length g hg
  simp only [cleanPermutation, List.length_append, swapPrefix_length]
  omega

end ExactQuantumFactoring.BooleanNetwork


end

end OAI
