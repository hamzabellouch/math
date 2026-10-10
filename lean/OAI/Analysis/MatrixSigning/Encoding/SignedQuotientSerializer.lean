import Mathlib
import OAI.Analysis.MatrixSigning.Encoding.UnsignedPairSerializer

namespace OAI

namespace KS.W19.SignedQuotientSerializer
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W19.UnsignedPairSerializer (registers registers_port registers_other)

def wire (sign : Bool) (payload : List Bool) : List Bool := sign :: KS.W01.frame payload

def emitProgram {k : Nat} (ports : Fin 3 ↪ Fin k) : Program k :=
  ofMachine (lift3 (KS.W28.PositiveWireSerializer.machine.withEntry (2 : Fin 5)) ports)
def reverseProgram {k : Nat} (ports : Fin 3 ↪ Fin k) : Program k :=
  ofMachine (lift3 KS.W29.NormalizeOutput.machine ports)
def program {k : Nat} (ports : Fin 3 ↪ Fin k) : Program k :=
  compose (emitProgram ports) (reverseProgram ports)

theorem emit_spec {k : Nat} (ports : Fin 3 ↪ Fin k) (spare : Fin k → List Bool)
    (sign : Bool) (payload : List Bool) :
    RunSpec (emitProgram ports) (registers ports spare [] payload [sign])
      (registers ports spare [] [] (wire sign payload).reverse) (2 * payload.length + 1) := by
  intro bits hb
  change (lift3 (KS.W28.PositiveWireSerializer.machine.withEntry (2 : Fin 5)) ports).run
    ⟨some (2 : Fin 5), registers ports spare [] payload [sign]⟩ bits = _
  apply lift3_run_eq
  · have hp : project ports (⟨some (2 : Fin 5), registers ports spare [] payload [sign]⟩ : Config k 5) =
        KS.W28.PositiveWireSerializer.cfg (some 2) [] payload [sign] := by
      apply congrArg (KS.W29.Config.mk (some (2 : Fin 5)))
      funext j
      fin_cases j <;> simp
    have hr := congrArg (fun c => (KS.W28.PositiveWireSerializer.machine.withEntry (2 : Fin 5)).run c bits) hp
    refine hr.trans ?_
    erw [KS.W29.BinaryMachine.withEntry_run,KS.W28.PositiveWireSerializer.run_den payload [sign] bits hb]
    apply congrArg (KS.W29.Config.mk none)
    funext j
    fin_cases j <;> simp [wire,List.reverse_cons]
  · intro j hj
    exact (registers_other ports spare _ _ _ j hj).trans
      (registers_other ports spare _ _ _ j hj).symm

theorem serialize_spec {k : Nat} (ports : Fin 3 ↪ Fin k) (spare : Fin k → List Bool)
    (sign : Bool) (payload : List Bool) :
    RunSpec (program ports) (registers ports spare [] payload [sign])
      (registers ports spare [] (wire sign payload) []) (4 * payload.length + 4) := by
  have h := (emit_spec ports spare sign payload).compose
    (UnsignedPairSerializer.reverse_spec ports spare (wire sign payload))
  have ht : (2 * payload.length + 1) + ((wire sign payload).length + 1) =
      4 * payload.length + 4 := by
    simp only [wire, List.length_cons, KS.W01.length_frame]
    omega
  rw [ht] at h
  exact h

end KS.W19.SignedQuotientSerializer

end OAI
