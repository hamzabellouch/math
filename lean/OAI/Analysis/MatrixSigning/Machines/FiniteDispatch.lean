import Mathlib
import OAI.Analysis.MatrixSigning.Machines.BinaryMachine

namespace OAI

section

namespace KS.W29
namespace FiniteDispatch

def decodeState {q : Nat} (index : Fin (54 * q)) : Fin q :=
  ⟨index.val / 54, by have h := index.isLt; omega⟩

def decodeHeads {q : Nat} (index : Fin (54 * q)) : Fin 27 :=
  ⟨index.val / 2 % 27, Nat.mod_lt _ (by decide)⟩

def decodeBit {q : Nat} (index : Fin (54 * q)) : Bool := index.val % 2 == 1

def compile {q : Nat} (initial : Fin q)
    (dispatch : Fin q → Fin 27 → Bool → Instruction q) : BinaryMachine :=
  ⟨q, initial, List.ofFn (fun index : Fin (54 * q) =>
    dispatch (decodeState index) (decodeHeads index) (decodeBit index))⟩

theorem decodeState_index {q : Nat} (s : Fin q) (c : Config q) (b : Bool) :
    decodeState ⟨transitionIndex s c b, transitionIndex_lt s c b⟩ = s := by
  apply Fin.ext
  have hh := headCode_lt q c
  have hb : bitCode b < 2 := by cases b <;> decide
  change (54 * s.val + 2 * headCode c + bitCode b) / 54 = s.val
  omega

theorem decodeHeads_index {q : Nat} (s : Fin q) (c : Config q) (b : Bool) :
    decodeHeads ⟨transitionIndex s c b, transitionIndex_lt s c b⟩ =
      ⟨headCode c, headCode_lt q c⟩ := by
  apply Fin.ext
  have hh := headCode_lt q c
  have hb : bitCode b < 2 := by cases b <;> decide
  change (54 * s.val + 2 * headCode c + bitCode b) / 2 % 27 = headCode c
  omega

theorem decodeBit_index {q : Nat} (s : Fin q) (c : Config q) (b : Bool) :
    decodeBit ⟨transitionIndex s c b, transitionIndex_lt s c b⟩ = b := by
  cases b with
  | false =>
      have h : transitionIndex s c false % 2 = 0 := by
        change (54 * s.val + 2 * headCode c + 0) % 2 = 0
        omega
      simp [decodeBit, h]
  | true =>
      have h : transitionIndex s c true % 2 = 1 := by
        change (54 * s.val + 2 * headCode c + 1) % 2 = 1
        omega
      simp [decodeBit, h]

theorem lookup_compile {q : Nat} (initial : Fin q)
    (dispatch : Fin q → Fin 27 → Bool → Instruction q)
    (s : Fin q) (c : Config q) (b : Bool) :
    (compile initial dispatch).table.getD (transitionIndex s c b) (Instruction.halt q) =
      dispatch s ⟨headCode c, headCode_lt q c⟩ b := by
  have hi := transitionIndex_lt s c b
  unfold compile
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp only [List.getElem_ofFn, decodeState_index, decodeHeads_index, decodeBit_index]

theorem step_compile {q : Nat} (initial : Fin q)
    (dispatch : Fin q → Fin 27 → Bool → Instruction q)
    (s : Fin q) («stacks» : Fin 3 → List Bool) (b : Bool) :
    (compile initial dispatch).step ⟨some s, «stacks»⟩ b =
      let c : Config q := ⟨some s, «stacks»⟩
      let i := dispatch s ⟨headCode c, headCode_lt q c⟩ b
      Config.mk i.next (fun j => (i.action j).apply («stacks» j)) := by
  simp only [BinaryMachine.step]
  erw [lookup_compile]
  rfl

end FiniteDispatch
end KS.W29

end

end OAI
