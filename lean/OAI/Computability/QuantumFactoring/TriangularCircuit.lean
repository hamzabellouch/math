import Mathlib
import OAI.Computability.QuantumFactoring.PackedEncoding
import OAI.Computability.QuantumFactoring.ControlledTranslation
import OAI.Computability.QuantumFactoring.RowNetwork
import OAI.Computability.QuantumFactoring.CleanPermutation
import OAI.Computability.QuantumFactoring.BitResidue
import OAI.Computability.QuantumFactoring.HadamardAction

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.Triangular
open scoped BigOperators
open BooleanNetwork

abbrev work (b : ℕ) := 159*b+6
abbrev width (b : ℕ) := (b+b)+(b+b)+work b

noncomputable def encode (b : ℕ) (u : Bits b × ZMod (2^b)) : Basis (width b) :=
  packed (work b) (Fin.append u.1 ((basisResidue b).symm u.2)) (fun _ => false)

lemma encode_injective (b : ℕ) : Function.Injective (encode b) := by
  intro u v h
  have he : Fin.append u.1 ((basisResidue b).symm u.2) =
      Fin.append v.1 ((basisResidue b).symm v.2) := by
    funext i
    have hh := congrFun h (⟨i.val,by dsimp [width,work]; omega⟩ : Fin (width b))
    simpa only [encode, packed_input] using hh
  apply Prod.ext
  · funext i
    have hh := congrFun he (i.castAdd b)
    simpa only [Fin.append_left] using hh
  · apply (basisResidue b).symm.injective
    funext i
    have hh := congrFun he (Fin.natAdd b i)
    simpa only [Fin.append_right] using hh

def dataWire {b : ℕ} (j : Fin b) : Fin (width b) := ⟨j.val,by have := j.isLt; dsimp [width,work]; omega⟩

lemma encode_bit {b : ℕ} (u : Bits b × ZMod (2^b)) (j : Fin b) :
    encode b u (dataWire j) = u.1 j := by
  change packed (work b) (Fin.append u.1 ((basisResidue b).symm u.2)) (fun _ => false)
    (⟨(j.castAdd b).val,by dsimp [width,work]; omega⟩ : Fin (width b)) = _
  rw [packed_input, Fin.append_left]

lemma encode_update {b : ℕ} (u : Bits b × ZMod (2^b)) (j : Fin b) (c : Bool) :
    Function.update (encode b u) (dataWire j) c = encode b (Function.update u.1 j c,u.2) := by
  unfold encode
  rw [show dataWire j = (⟨(j.castAdd b).val,by dsimp [width,work]; omega⟩ : Fin (width b)) by rfl,
    packed_update_input, append_update_left]

lemma translation_count_forward {b : ℕ} (j : Fin b) :
    (ControlledTranslation.forward (rowNetwork j)).net.count ≤ work b := by
  have h := ControlledTranslation.forward_count (rowNetwork j)
  rw [rowNetwork_count] at h
  dsimp [work]
  omega

lemma translation_count_backward {b : ℕ} (j : Fin b) :
    (ControlledTranslation.backward (rowNetwork j)).net.count ≤ work b := by
  have h := ControlledTranslation.backward_count (rowNetwork j)
  rw [rowNetwork_count] at h
  dsimp [work]
  omega

def translation {b : ℕ} (j : Fin b) : List (Instruction (width b)) :=
  cleanPermutation (ControlledTranslation.forward (rowNetwork j))
    (ControlledTranslation.backward (rowNetwork j))
    (translation_count_forward j) (translation_count_backward j)

noncomputable def rowPerm {b : ℕ} (j : Fin b) : Equiv.Perm (Bits b × ZMod (2^b)) where
  toFun u := (u.1,u.2+(rowShift j u.1 : ZMod (2^b)))
  invFun u := (u.1,u.2-(rowShift j u.1 : ZMod (2^b)))
  left_inv u := by simp
  right_inv u := by simp

lemma translate_encode {b : ℕ} (j : Fin b) (u : Bits b × ZMod (2^b)) :
    ControlledTranslation.translate (fun d => bitsValue ((rowNetwork j).eval d))
      (Fin.append u.1 ((basisResidue b).symm u.2)) =
      Fin.append u.1 ((basisResidue b).symm (u.2+(rowShift j u.1 : ZMod (2^b)))) := by
  simp only [ControlledTranslation.translate, ControlledTranslation.dataPart_append,
    ControlledTranslation.phasePart_append, bitsValue_residue_add]
  rw [basisResidue_eq, rowNetwork_number]

lemma translation_basis {b : ℕ} (j : Fin b) (u : Bits b × ZMod (2^b)) :
    (programMatrix (translation j)).mulVec (basisVector (encode b u)) =
      basisVector (encode b (rowPerm j u)) := by
  unfold translation encode
  rw [cleanPermutation_basis _ _ _ _ _ (ControlledTranslation.forward_backward _ _),
    ControlledTranslation.forward_correct, translate_encode]
  rfl

lemma translation_apply {b : ℕ} (j : Fin b) (ψ : Bits b × ZMod (2^b) → ℂ) :
    (programMatrix (translation j)).mulVec (encodeState (encode b) ψ) =
      encodeState (encode b) (ψ ∘ (rowPerm j).symm) :=
  matrix_encode_permutation _ _ _ (translation_basis j) ψ

def rowCircuit {b : ℕ} (j : Fin b) : List (Instruction (width b)) :=
  [hadamardAt (dataWire j)] ++ translation j

lemma rowCircuit_apply {b : ℕ} (j : Fin b) (ψ : Bits b × ZMod (2^b) → ℂ) :
    (programMatrix (rowCircuit j)).mulVec (encodeState (encode b) ψ) =
      encodeState (encode b) (fun u =>
        (ψ (Function.update u.1 j false,u.2-(rowShift j u.1 : ZMod (2^b))) +
          (if u.1 j then (-1:ℂ) else 1)*
            ψ (Function.update u.1 j true,u.2-(rowShift j u.1 : ZMod (2^b)))) /
              (Real.sqrt 2:ℂ)) := by
  rw [rowCircuit, programMatrix_append, programMatrix_singleton, ← Matrix.mulVec_mulVec,
    encoded_hadamard (encode b) j (dataWire j) (fun u => encode_bit u j)
      (fun u c => encode_update u j c), translation_apply]
  congr 1
  funext u
  exact localHadamard_apply j ψ ((rowPerm j).symm u)

def triPrefix (b : ℕ) : (k : ℕ) → k ≤ b → List (Instruction (width b))
  | 0, _ => []
  | k+1, h => triPrefix b k (by omega) ++ rowCircuit ⟨k,by omega⟩

lemma triPrefix_apply {b : ℕ} (x : Bits b) (χ : ZMod (2^b) → ℂ) (k : ℕ) (hk : k ≤ b) :
    (programMatrix (triPrefix b k hk)).mulVec
        (encodeState (encode b) (fun u => if u.1=x then χ u.2 else 0)) =
      encodeState (encode b) (fun u =>
        evolve (fun j z => (rowShift j z : ZMod (2^b))) x χ k hk u.1 u.2) := by
  induction k with
  | zero => rw [triPrefix, programMatrix_nil, Matrix.one_mulVec]; rfl
  | succ k ih =>
    rw [triPrefix, programMatrix_append, ← Matrix.mulVec_mulVec, ih (by omega), rowCircuit_apply]
    rfl

lemma rowCircuit_length {b : ℕ} (j : Fin b) :
    (rowCircuit j).length ≤ 998*b+49 := by
  have h := cleanPermutation_length (ControlledTranslation.forward (rowNetwork j))
    (ControlledTranslation.backward (rowNetwork j))
    (translation_count_forward j) (translation_count_backward j)
  have hf := ControlledTranslation.forward_count (rowNetwork j)
  have hg := ControlledTranslation.backward_count (rowNetwork j)
  rw [rowNetwork_count] at hf hg
  change (translation j).length ≤ _ at h
  simp only [rowCircuit, List.length_append, List.length_singleton]
  omega

lemma triPrefix_length (b k : ℕ) (hk : k ≤ b) :
    (triPrefix b k hk).length ≤ k*(998*b+49) := by
  induction k with
  | zero => simp [triPrefix]
  | succ k ih =>
    have hp := ih (by omega)
    have hr := rowCircuit_length (⟨k,by omega⟩ : Fin b)
    simp only [triPrefix, List.length_append]
    nlinarith

end ExactQuantumFactoring.Triangular


end

end OAI
