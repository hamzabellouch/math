import Mathlib
import OAI.Computability.QuantumFactoring.OrderSampleCircuit

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open BooleanNetwork

lemma encodeState_comp {α : Type*} [Fintype α] {p q : ℕ}
    (e : α → Basis p) (f : Basis p → Basis q) (ψ : α → ℂ) :
    encodeState f (encodeState e ψ) = encodeState (f ∘ e) ψ := by
  classical
  change encodeState f (∑ a, ψ a • basisVector (e a)) = _
  rw [encodeState_sum]
  simp_rw [encodeState_smul,encodeState_basis]
  rfl

namespace Triangular

def dataRegister (b : ℕ) : Register b (width b) :=
  ⟨dataWire,by
    intro i j h
    exact Fin.ext (congrArg (fun t : Fin (width b) => t.val) h)⟩

lemma encode_data {b : ℕ} (u : Bits b × ZMod (2^b)) :
    encode b u ∘ dataRegister b = u.1 := by
  funext i
  exact encode_bit u i

lemma encode_outside_data {b : ℕ} (x y : Bits b) (z : ZMod (2^b))
    (i : (dataRegister b).Unused) : encode b (x,z) i.val = encode b (y,z) i.val := by
  have hi : ¬i.val.val < b := by
    intro hi
    exact i.property ⟨i.val.val,hi⟩ rfl
  by_cases hh : i.val.val < b+b
  · have he : i.val = (⟨(Fin.natAdd b (⟨i.val.val-b,by omega⟩ : Fin b)).val,
        by dsimp [width,work]; omega⟩ : Fin (width b)) := by
      apply Fin.ext
      change i.val.val = b+(i.val.val-b)
      omega
    rw [he]
    simp only [encode,packed_input,Fin.append_right]
  · simp [encode,packed,hh]

lemma encode_replace_data {b : ℕ} (x y : Bits b) (z : ZMod (2^b)) :
    (dataRegister b).replace (encode b (x,z)) y = encode b (y,z) := by
  apply (dataRegister b).split.injective
  apply Prod.ext
  · rw [Register.replace,Equiv.apply_symm_apply]
    exact (encode_data (y,z)).symm
  · funext i
    change (dataRegister b).replace (encode b (x,z)) y i.val = _
    rw [Register.replace_outside]
    exact encode_outside_data x y z i

def uniformPreparation (b : ℕ) : List (Instruction (width b)) :=
  (hadamardPrefix b b le_rfl).map (Instruction.place (dataRegister b))

lemma uniformPreparation_length (b : ℕ) : (uniformPreparation b).length=b := by
  simp [uniformPreparation,hadamardPrefix_length]

lemma uniformPreparation_zero (b : ℕ) :
    (programMatrix (uniformPreparation b)).mulVec
      (basisVector (encode b ((fun _ => false),0))) =
    encodeState (fun x => encode b (x,0))
      (fun _ => (Real.sqrt ((2:ℝ)^b):ℂ)⁻¹) := by
  rw [uniformPreparation,Register.placed_basis_state,encode_data,hadamards_zero]
  change encodeState (fun y => (dataRegister b).replace (encode b ((fun _ => false),0)) y)
    (fun _ => (Real.sqrt 2:ℂ)⁻¹^b) = _
  simp_rw [encode_replace_data,hadamard_normalization]

end Triangular
namespace OrderSample

def initial (w b : ℕ) : List (Instruction (width w b)) :=
  firstProgram w (scratch w b) (rightProgram (w+w) (Triangular.uniformPreparation b))

lemma initial_length (w b : ℕ) : (initial w b).length=b := by
  simp [initial,firstProgram_length,rightProgram,Triangular.uniformPreparation_length]

lemma initial_zero (w b : ℕ) (a m : Basis w) :
    (programMatrix (initial w b)).mulVec
      (basisVector (word a m (fun _ => false) (fun _ => false))) = uniformInput w b a m := by
  rw [initial,word,firstProgram_basis,inputWord,rightProgram_basis,
    Triangular.uniformPreparation_zero,encodeState_comp,encodeState_comp]
  rfl

def completeSampler (w s : ℕ) : List (Instruction (width w (s+2))) :=
  initial w (s+2) ++ program w s

lemma completeSampler_length (w s : ℕ) : (completeSampler w s).length ≤
    (s+2)+4*scratch w (s+2)+2*w+(s+2)*(998*(s+2)+49)+2*(s+5) := by
  have h := program_length w s
  simp only [completeSampler,List.length_append,initial_length]
  omega

/-- Physical sampler starts from a computational basis vector, not an assumed
uniform state. Its selected entry is the exact residue-class interference sum. -/
theorem completeSampler_amplitude {w s : ℕ} (a m : Basis w) (y : Basis (s+2)) (u : Basis w)
    (hm : 2 ≤ (bitsValue m).toNat) :
    (programMatrix (completeSampler w s)).mulVec
      (basisVector (word a m (fun _ => false) (fun _ => false))) (word a m y u) =
      ((2^(s+2):ℕ):ℂ)⁻¹ * ∑ x ∈ Finset.range (2^(s+2)),
        if (bitsValue a).toNat^x % (bitsValue m).toNat=(bitsValue u).toNat
        then OrderTrial.phase ((Triangular.outputNumber y:ℝ)*x/(2^(s+2):ℕ)) else 0 := by
  rw [completeSampler,programMatrix_append,← Matrix.mulVec_mulVec,initial_zero]
  exact program_amplitude_range a m y u hm

end OrderSample
end ExactQuantumFactoring


end

end OAI
