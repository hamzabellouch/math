import Mathlib
import OAI.Computability.QuantumFactoring.FactoringRelabel

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open BooleanNetwork BitArithmetic Exactness
namespace PhysicalTree

lemma paddedLength_pos (ℓ : ℕ) : 0<paddedLength ℓ := by
  unfold paddedLength;omega
lemma finalRegister_bound (ℓ : ℕ) :
    ℓ+1≤amplifiedWidth (paddedLength ℓ) (paddedLength_pos ℓ) := by
  have h:=quarterWidth_input (paddedLength ℓ)
  have hl : ℓ≤paddedLength ℓ:=le_max_right _ _
  change ℓ+1≤quarterWidth (paddedLength ℓ)+1+reflectWork (paddedLength ℓ) (paddedLength_pos ℓ)
  omega

def finalRegister (ℓ : ℕ) : Register
    (readoutWidth (paddedLength ℓ) (paddedLength_pos ℓ))
    (readoutWidth (paddedLength ℓ) (paddedLength_pos ℓ)) :=
  relocate (amplifiedWidth (paddedLength ℓ) (paddedLength_pos ℓ))
    (paddedLength ℓ*paddedLength ℓ) ℓ
    (readoutWork (paddedLength ℓ) (paddedLength_pos ℓ)) (finalRegister_bound ℓ)

def finalCircuit (ℓ : ℕ) : Circuit where
  qubits:=readoutWidth (paddedLength ℓ) (paddedLength_pos ℓ)
  instructions:=(factoringProgram (paddedLength ℓ) (paddedLength_pos ℓ)).map
    (Instruction.place (finalRegister ℓ))

lemma final_input (ℓ N : ℕ) (hb : N<2^ℓ) :
    inputBasis (finalCircuit ℓ).qubits ℓ N ∘ finalRegister ℓ=
      factoringZero (paddedLength ℓ) N (paddedLength_pos ℓ) := by
  dsimp only [finalCircuit]
  rw [finalRegister,relocate_input]
  rw [shiftedInput_pad _ (paddedLength ℓ) ℓ N (le_max_right _ _) hb]
  exact (factoringZero_shifted _ _ _).symm

lemma final_register_output (ℓ : ℕ) (j : Fin (paddedLength ℓ*paddedLength ℓ)) :
    finalRegister ℓ (targetRegister (amplifiedWidth (paddedLength ℓ) (paddedLength_pos ℓ))
      (paddedLength ℓ*paddedLength ℓ) (readoutWork (paddedLength ℓ) (paddedLength_pos ℓ)) j)=
    ⟨ℓ+j.val,by have:=j.isLt;have:=finalRegister_bound ℓ;dsimp only [readoutWidth];omega⟩ := by
  exact relocate_output _ _ _ _ _ j

lemma final_output (ℓ : ℕ) (z : Basis (readoutWidth (paddedLength ℓ) (paddedLength_pos ℓ)))
    (x : Basis (readoutWidth (paddedLength ℓ) (paddedLength_pos ℓ))) :
    outputList ℓ ((finalRegister ℓ).replace z x)=
      guessWords (paddedLength ℓ) (factoringResult (paddedLength ℓ) (paddedLength_pos ℓ) x) := by
  dsimp only [outputList,guessWords]
  apply congrArg List.ofFn
  funext a
  rw [bitsValue_toNat,←Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  let k : Fin (paddedLength ℓ*paddedLength ℓ):=finProdFinEquiv (a,j)
  have hk : k.val=a.val*paddedLength ℓ+j.val:=by
    change j.val+paddedLength ℓ*a.val=a.val*paddedLength ℓ+j.val
    ring
  have hh:=final_register_output ℓ k
  have hb : ℓ+a.val*paddedLength ℓ+j.val<readoutWidth (paddedLength ℓ) (paddedLength_pos ℓ) := by
    have hi:=(finalRegister ℓ (targetRegister _ _ _ k)).isLt
    rw [hh] at hi
    dsimp only at hi
    omega
  simp only [readBit,dite_eq_left hb]
  have he : (⟨ℓ+a.val*paddedLength ℓ+j.val,hb⟩ : Fin (readoutWidth (paddedLength ℓ) (paddedLength_pos ℓ)))=
      finalRegister ℓ (targetRegister _ _ _ k) := by
    rw [hh];apply Fin.ext;dsimp only;omega
  rw [he,Register.replace_inside]
  change (if x (targetRegister _ _ _ k) then 2^j.val else 0)=
    2^j.val*(x (targetRegister _ _ _ k)).toNat
  cases x (targetRegister _ _ _ k) <;> simp

lemma finalCircuit_qubits (ℓ : ℕ) :
    ℓ+(paddedLength ℓ)^2≤(finalCircuit ℓ).qubits := by
  have h:=finalRegister_bound ℓ
  change ℓ+(paddedLength ℓ)^2≤amplifiedWidth _ _+paddedLength ℓ*paddedLength ℓ+readoutWork _ _
  rw [pow_two]
  omega

theorem finalCircuit_exact (ℓ N : ℕ) (hN : 2≤N) (hb : N<2^ℓ) :
    (finalCircuit ℓ).correctProbability ℓ N=1 := by
  have hh : 128≤paddedLength ℓ:=le_max_left _ _
  have hb' : N<2^paddedLength ℓ:=lt_of_lt_of_le hb (Nat.pow_le_pow_right (by omega) (le_max_right _ _))
  change outcomeMass (fun x=>CorrectEncoding N (paddedLength ℓ) (outputList ℓ x))
    ((finalCircuit ℓ).apply (basisVector (inputBasis (finalCircuit ℓ).qubits ℓ N)))=1
  rw [Circuit.apply_eq_matrix]
  change outcomeMass (fun x : Basis (readoutWidth (paddedLength ℓ) (paddedLength_pos ℓ))=>
      CorrectEncoding N (paddedLength ℓ) (outputList ℓ x))
    ((programMatrix ((factoringProgram (paddedLength ℓ) (paddedLength_pos ℓ)).map
      (Instruction.place (finalRegister ℓ)))).mulVec
      (basisVector (inputBasis (readoutWidth (paddedLength ℓ) (paddedLength_pos ℓ)) ℓ N)))=1
  rw [Register.placed_basis_state]
  have hin := final_input ℓ N hb
  change inputBasis (readoutWidth (paddedLength ℓ) (paddedLength_pos ℓ)) ℓ N ∘ finalRegister ℓ = _ at hin
  rw [hin]
  rw [outcomeMass_encode _ (Register.replace_injective _ _)]
  have he : ((fun x=>CorrectEncoding N (paddedLength ℓ) (outputList ℓ x)) ∘
      ((finalRegister ℓ).replace (inputBasis (readoutWidth (paddedLength ℓ) (paddedLength_pos ℓ)) ℓ N)))=
      (fun x=>CorrectEncoding N (paddedLength ℓ)
        (guessWords (paddedLength ℓ) (factoringResult (paddedLength ℓ) (paddedLength_pos ℓ) x))) := by
    funext x
    simp only [Function.comp_apply,final_output]
  rw [he]
  exact factoringProgram_exact hh hN hb'

/-- Discharges exactly the input/output clause for one explicit length-only
family. This does NOT assert the outstanding resource or TM2-uniformity clauses. -/
theorem finalCircuit_spec (ℓ N : ℕ) (hN : 2≤N) (hs : N.size=ℓ) :
    ℓ+(paddedLength ℓ)^2≤(finalCircuit ℓ).qubits ∧
      (finalCircuit ℓ).correctProbability ℓ N=1 := by
  refine ⟨finalCircuit_qubits ℓ,finalCircuit_exact ℓ N hN ?_⟩
  rw [←hs]
  exact Nat.lt_size_self N

lemma finalCircuit_length (ℓ : ℕ) :
    (finalCircuit ℓ).instructions.length=
      (factoringProgram (paddedLength ℓ) (paddedLength_pos ℓ)).length := by
  exact List.length_map _

end PhysicalTree
end ExactQuantumFactoring


end

end OAI
