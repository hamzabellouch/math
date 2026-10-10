import Mathlib
import OAI.Analysis.MatrixSigning.Machines.FixedCanonicalize
import OAI.Analysis.MatrixSigning.Arithmetic.DivisionMachine

namespace OAI

namespace KS.W19.DivisionOutput
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W19.DivisionMachine («stacks»)

def quotientPorts : Fin 3 ↪ Fin 10 := ⟨![0,5,8], by decide⟩
def remainderPorts : Fin 3 ↪ Fin 10 := ⟨![0,4,8], by decide⟩
def pairPorts : Fin 3 ↪ Fin 10 := ⟨![5,4,8], by decide⟩
def canonQ : Program 10 := FixedCanonicalize.program quotientPorts
def canonR : Program 10 := FixedCanonicalize.program remainderPorts
def emit : Program 10 := UnsignedPairSerializer.program pairPorts
def tailProgram : Program 10 := compose canonR emit
def program : Program 10 := compose canonQ tailProgram

def canonical (xs : List Bool) : List Bool := Computability.encodeNat (bitsValue xs)
def pairWire (q r : List Bool) : List Bool := KS.W01.frame (canonical q) ++ KS.W01.frame (canonical r)

theorem canonical_length (xs : List Bool) : (canonical xs).length ≤ xs.length := by
  rw [canonical, ← trimBits_eq_encodeNat]
  exact trimBits_length_le xs

theorem quotient_spec (d q r : List Bool) :
    RunSpec canonQ («stacks» d [] q r [] [] [] [])
      («stacks» d [] (canonical q) r [] [] [] []) (2 * q.length + 2) := by
  have h := FixedCanonicalize.canonicalize_spec quotientPorts («stacks» d [] q r [] [] [] []) [] q
  have hi : UnsignedPairSerializer.registers quotientPorts («stacks» d [] q r [] [] [] []) [] q [] =
      «stacks» d [] q r [] [] [] [] := by funext j; fin_cases j <;> rfl
  have ho : UnsignedPairSerializer.registers quotientPorts («stacks» d [] q r [] [] [] []) [] (canonical q) [] =
      «stacks» d [] (canonical q) r [] [] [] [] := by funext j; fin_cases j <;> rfl
  dsimp only [canonical] at ho
  simp only [hi, ho] at h
  exact h

theorem remainder_spec (d q r : List Bool) :
    RunSpec canonR («stacks» d [] q r [] [] [] [])
      («stacks» d [] q (canonical r) [] [] [] []) (2 * r.length + 2) := by
  have h := FixedCanonicalize.canonicalize_spec remainderPorts («stacks» d [] q r [] [] [] []) [] r
  have hi : UnsignedPairSerializer.registers remainderPorts («stacks» d [] q r [] [] [] []) [] r [] =
      «stacks» d [] q r [] [] [] [] := by funext j; fin_cases j <;> rfl
  have ho : UnsignedPairSerializer.registers remainderPorts («stacks» d [] q r [] [] [] []) [] (canonical r) [] =
      «stacks» d [] q (canonical r) [] [] [] [] := by funext j; fin_cases j <;> rfl
  dsimp only [canonical] at ho
  simp only [hi, ho] at h
  exact h

theorem emit_spec (d q r : List Bool) :
    RunSpec emit («stacks» d [] (canonical q) (canonical r) [] [] [] [])
      («stacks» d [] [] (pairWire q r) [] [] [] [])
      (4 * (canonical q).length + 4 * (canonical r).length + 5) := by
  have h := UnsignedPairSerializer.serialize_spec pairPorts
    («stacks» d [] (canonical q) (canonical r) [] [] [] []) (canonical q) (canonical r)
  have hi : UnsignedPairSerializer.registers pairPorts
      («stacks» d [] (canonical q) (canonical r) [] [] [] []) (canonical q) (canonical r) [] =
      «stacks» d [] (canonical q) (canonical r) [] [] [] [] := by funext j; fin_cases j <;> rfl
  have ho : UnsignedPairSerializer.registers pairPorts
      («stacks» d [] (canonical q) (canonical r) [] [] [] []) [] (pairWire q r) [] =
      «stacks» d [] [] (pairWire q r) [] [] [] [] := by funext j; fin_cases j <;> rfl
  dsimp only [pairWire] at ho
  simp only [UnsignedPairSerializer.wire,hi,ho] at h
  exact h

theorem output_spec (d q r : List Bool) :
    RunSpec program («stacks» d [] q r [] [] [] [])
      («stacks» d [] [] (pairWire q r) [] [] [] []) (6 * q.length + 6 * r.length + 9) := by
  have h := (quotient_spec d q r).compose
    ((remainder_spec d (canonical q) r).compose (emit_spec d q r))
  apply h.mono
  have hq := canonical_length q
  have hr := canonical_length r
  omega

theorem read_pair (q r : List Bool) :
    KS.W01.readNat (pairWire q r) = some (bitsValue q, KS.W01.encodeNat (bitsValue r)) := by
  unfold pairWire canonical
  exact KS.W01.readNat_encode_append (bitsValue q) (KS.W01.encodeNat (bitsValue r))

end KS.W19.DivisionOutput

end OAI
