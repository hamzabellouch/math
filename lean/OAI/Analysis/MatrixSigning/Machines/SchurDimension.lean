import Mathlib
import OAI.Analysis.MatrixSigning.Machines.SignedSerializePrimitives
import OAI.Analysis.MatrixSigning.Machines.SchurCounters
import OAI.Analysis.MatrixSigning.Machines.SchurReadStage
import OAI.Analysis.MatrixSigning.Machines.CanonicalUnarySpec

namespace OAI

namespace KS.W07.SchurDimension
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open SchurReadStage

def predecessorPorts : Fin 3 ↪ Fin 32 := ⟨![0,1,2], by decide⟩
def predecessor : Program 32 := compose
  (copyProgram 26 0 (by decide) (by decide) (by decide))
  (compose (SchurCounters.pushProgram 1 true)
    (compose (KS.W01.SignedSerializePrimitives.subtractProgram predecessorPorts)
      (WireAppend.program 1 30 16)))

def predecessorTicks (n : ℕ) : ℕ := (2*(Computability.encodeNat (n+1)).length+2) +
  (1 + (2*(max (Computability.encodeNat (n+1)).length 1+1) +
    (2*(Computability.encodeNat n).length+2)))

theorem predecessor_spec (s : Fin 32 → List Bool) (n : ℕ)
    (hd : s 26 = Computability.encodeNat (n+1))
    (h0 : s 0 = []) (h1 : s 1 = []) (h2 : s 2 = []) (h16 : s 16 = []) (h30 : s 30 = []) :
    RunSpec predecessor s (Function.update s 30 (Computability.encodeNat n)) (predecessorTicks n) := by
  have hc := copy_spec 26 0 (by decide) (by decide) (by decide) s h0 h16
  rw [hd] at hc
  have hp := SchurCounters.push_spec (1 : Fin 32) true
    (Function.update s 0 (Computability.encodeNat (n+1)))
  have hs := KS.W01.SignedSerializePrimitives.decrement_spec predecessorPorts s
    (Computability.encodeNat (n+1))
  rw [KS.W01.WireMagnitude.decrement_encode_succ] at hs
  have hi : Function.update (Function.update s 0 (Computability.encodeNat (n+1))) 1
      (true :: (Function.update s 0 (Computability.encodeNat (n+1))) 1) =
      KS.W28.FixedPositiveSerializer.registers predecessorPorts s
        (Computability.encodeNat (n+1)) [true] [] := by
    funext j; fin_cases j <;> simp [KS.W28.FixedPositiveSerializer.registers,predecessorPorts,h1,h2]
  rw [hi] at hp
  have ho : KS.W28.FixedPositiveSerializer.registers predecessorPorts s []
      (Computability.encodeNat n) [] = Function.update s 1 (Computability.encodeNat n) := by
    funext j; fin_cases j <;> simp [KS.W28.FixedPositiveSerializer.registers,predecessorPorts,h0,h2]
  rw [ho] at hs
  have hm := WireAppend.spec (1 : Fin 32) 30 16 (by decide) (by decide) (by decide)
    (Function.update s 1 (Computability.encodeNat n)) (by simpa using h16)
  have hout : WireAppend.after 1 30 (Function.update s 1 (Computability.encodeNat n)) =
      Function.update s 30 (Computability.encodeNat n) := by
    funext j; fin_cases j <;> simp [WireAppend.after,h1,h30]
  rw [hout] at hm
  exact hc.compose (hp.compose (hs.compose hm))

def counterPort (column : Bool) : Fin 32 := if column then 25 else 24

def unaryPorts (column : Bool) : Fin 3 ↪ Fin 32 :=
  ⟨![0,counterPort column,1], by cases column <;> decide⟩

@[simp] private theorem unaryPorts_apply (column : Bool) (i : Fin 3) :
    unaryPorts column i = ![0,counterPort column,1] i := rfl

def unaryProgram (column : Bool) : Program 32 := compose
  (copyProgram 30 0 (by decide) (by decide) (by decide))
  (liftPorts KS.W03.BinaryToUnary.program (unaryPorts column))

theorem unary_spec (column : Bool) (s : Fin 32 → List Bool) (n : ℕ)
    (hd : s 30 = Computability.encodeNat n)
    (h0 : s 0 = []) (h1 : s 1 = []) (h16 : s 16 = []) (ht : s (counterPort column) = []) :
    RunSpec (unaryProgram column) s
      (Function.update s (counterPort column) (List.replicate n true))
      (4*n + 6*(Computability.encodeNat n).length+4) := by
  have hc := copy_spec 30 0 (by decide) (by decide) (by decide) s h0 h16
  rw [hd] at hc
  have hsmall : RunSpec KS.W03.BinaryToUnary.program
      ![Computability.encodeNat n,[],[]] ![[],List.replicate n true,[]]
      (4*n + 4*(Computability.encodeNat n).length+2) := KS.W07.canonicalUnary_spec n
  have hu : RunSpec (liftPorts KS.W03.BinaryToUnary.program (unaryPorts column))
      (Function.update s 0 (Computability.encodeNat n))
      (Function.update s (counterPort column) (List.replicate n true))
      (4*n + 4*(Computability.encodeNat n).length+2) := by
    apply KS.W01.FixedPortRunSpec.lift_runSpec _ (unaryPorts column) _ _ _ _ _ hsmall
    · intro j; fin_cases j <;> cases column <;> simp_all [counterPort]
    · intro j; fin_cases j <;> cases column <;> simp_all [counterPort]
    · intro j hj
      have hzero := hj 0
      have htarget := hj 1
      change j ≠ 0 at hzero
      change j ≠ counterPort column at htarget
      simp [Function.update_of_ne,hzero,htarget]
  have h := hc.compose hu
  have he : (2*(Computability.encodeNat n).length+2) +
      (4*n+4*(Computability.encodeNat n).length+2) = 4*n+6*(Computability.encodeNat n).length+4 := by omega
  simpa only [unaryProgram,he] using h

end KS.W07.SchurDimension

end OAI
