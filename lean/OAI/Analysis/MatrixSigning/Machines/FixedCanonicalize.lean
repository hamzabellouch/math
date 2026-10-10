import Mathlib
import OAI.Analysis.MatrixSigning.Machines.BinaryStackMoves
import OAI.Analysis.MatrixSigning.Machines.BinaryTrimMachine
import OAI.Analysis.MatrixSigning.Machines.FixedRun
import OAI.Analysis.MatrixSigning.Encoding.UnsignedPairSerializer

namespace OAI

namespace KS.W19.FixedCanonicalize
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W19.UnsignedPairSerializer (registers registers_port registers_other)

def reverseProgram {k : Nat} (ports : Fin 3 ↪ Fin k) : Program k :=
  KS.W04.BinaryStackMoves.moveProgram (ports 1) (ports 2)
def trimProgram {k : Nat} (ports : Fin 3 ↪ Fin k) : Program k :=
  ofMachine (lift3 BinaryTrimMachine.machine ports)
def program {k : Nat} (ports : Fin 3 ↪ Fin k) : Program k :=
  compose (reverseProgram ports) (trimProgram ports)

theorem reverse_spec {k : Nat} (ports : Fin 3 ↪ Fin k) (spare : Fin k → List Bool)
    (input payload : List Bool) :
    RunSpec (reverseProgram ports) (registers ports spare input payload [])
      (registers ports spare input [] payload.reverse) (payload.length + 1) := by
  intro bits hb
  have hne : ports 1 ≠ ports 2 := fun h => (by decide : (1 : Fin 3) ≠ 2) (ports.injective h)
  have hl : bits.length = (registers ports spare input payload [] (ports 1)).length + 1 := by
    simpa using hb
  have h := KS.W04.BinaryStackMoves.run_move_stacks (ports 1) (ports 2) hne
    (registers ports spare input payload []) bits hl
  refine h.trans ?_
  apply KS.W19.FixedRun.config_ext
  · rfl
  · intro j
    by_cases h1 : j = ports 1
    · subst j
      simp [KS.W04.BinaryStackMoves.twoConfig, registers, ports.injective.eq_iff]
    by_cases h2 : j = ports 2
    · subst j
      simp [KS.W04.BinaryStackMoves.twoConfig, registers, ports.injective.eq_iff]
    simp [KS.W04.BinaryStackMoves.twoConfig, registers, h1, h2]

theorem trim_spec {k : Nat} (ports : Fin 3 ↪ Fin k) (spare : Fin k → List Bool)
    (input payload : List Bool) :
    RunSpec (trimProgram ports) (registers ports spare input [] payload.reverse)
      (registers ports spare input (Computability.encodeNat (bitsValue payload)) [])
      (payload.length + 1) := by
  intro bits hb
  change (lift3 BinaryTrimMachine.machine ports).run
    ⟨some (0 : Fin 2), registers ports spare input [] payload.reverse⟩ bits = _
  apply lift3_run_eq
  · have hp : project ports (⟨some (0 : Fin 2), registers ports spare input [] payload.reverse⟩ : Config k 2) =
        BinaryTrimMachine.cfg (some 0) input [] payload.reverse := by
      apply congrArg (KS.W29.Config.mk (some (0 : Fin 2)))
      funext j
      fin_cases j <;> simp
    have hr := congrArg (fun c => BinaryTrimMachine.machine.run c bits) hp
    refine hr.trans ?_
    refine (BinaryTrimMachine.run_payload input payload bits hb).trans ?_
    apply congrArg (KS.W29.Config.mk none)
    funext j
    fin_cases j <;> simp
  · intro j hj
    exact (registers_other ports spare _ _ _ j hj).trans
      (registers_other ports spare _ _ _ j hj).symm

theorem canonicalize_spec {k : Nat} (ports : Fin 3 ↪ Fin k) (spare : Fin k → List Bool)
    (input payload : List Bool) :
    RunSpec (program ports) (registers ports spare input payload [])
      (registers ports spare input (Computability.encodeNat (bitsValue payload)) [])
      (2 * payload.length + 2) := by
  have h := (reverse_spec ports spare input payload).compose (trim_spec ports spare input payload)
  have ht : (payload.length + 1) + (payload.length + 1) = 2 * payload.length + 2 := by omega
  rw [ht] at h
  exact h

end KS.W19.FixedCanonicalize

end OAI
