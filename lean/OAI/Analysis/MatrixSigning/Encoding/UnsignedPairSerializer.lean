import Mathlib
import OAI.Analysis.MatrixSigning.Machines.MachineCombinators
import OAI.Analysis.MatrixSigning.Encoding.PositiveWireSerializer
import OAI.Analysis.MatrixSigning.Machines.NormalizeOutput

namespace OAI

namespace KS.W19.UnsignedPairSerializer
open KS.W28
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def registers {k : ℕ} (ports : Fin 3 ↪ Fin k) (spare : Fin k → List Bool)
    (xs ys zs : List Bool) : Fin k → List Bool := fun j =>
  if j = ports 0 then xs else if j = ports 1 then ys else if j = ports 2 then zs else spare j

@[simp] theorem registers_port {k : ℕ} (ports : Fin 3 ↪ Fin k)
    (spare : Fin k → List Bool) (xs ys zs : List Bool) (i : Fin 3) :
    registers ports spare xs ys zs (ports i) =
      if i = 0 then xs else if i = 1 then ys else zs := by
  fin_cases i <;> simp [registers, ports.injective.eq_iff]

theorem registers_other {k : ℕ} (ports : Fin 3 ↪ Fin k)
    (spare : Fin k → List Bool) (xs ys zs : List Bool) (j : Fin k)
    (hj : ∀ i, j ≠ ports i) : registers ports spare xs ys zs j = spare j := by
  simp [registers, hj 0, hj 1, hj 2]

def wire (xs ys : List Bool) : List Bool := KS.W01.frame xs ++ KS.W01.frame ys

theorem wire_length (xs ys : List Bool) : (wire xs ys).length = 2 * xs.length + 2 * ys.length + 2 := by
  simp only [wire, List.length_append, KS.W01.length_frame]
  omega

def emitProgram {k : ℕ} (ports : Fin 3 ↪ Fin k) : Program k :=
  ofMachine (lift3 (PositiveWireSerializer.machine.withEntry (0 : Fin 5)) ports)

def reverseProgram {k : ℕ} (ports : Fin 3 ↪ Fin k) : Program k :=
  ofMachine (lift3 KS.W29.NormalizeOutput.machine ports)

def program {k : ℕ} (ports : Fin 3 ↪ Fin k) : Program k :=
  compose (emitProgram ports) (reverseProgram ports)

theorem emit_spec {k : ℕ} (ports : Fin 3 ↪ Fin k) (spare : Fin k → List Bool)
    (xs ys : List Bool) :
    RunSpec (emitProgram ports) (registers ports spare xs ys [])
      (registers ports spare [] [] (wire xs ys).reverse)
      (2 * xs.length + 2 * ys.length + 2) := by
  intro bits hbits
  change (lift3 (PositiveWireSerializer.machine.withEntry (0 : Fin 5)) ports).run
    ⟨some (0 : Fin 5), registers ports spare xs ys []⟩ bits = _
  apply lift3_run_eq
  · have hp : project ports (⟨some 0, registers ports spare xs ys []⟩ : Config k 5) =
        PositiveWireSerializer.cfg (some 0) xs ys [] := by
      apply congrArg (KS.W29.Config.mk (some (0 : Fin 5)))
      funext j
      fin_cases j <;> simp
    have hr := congrArg
      (fun c => (PositiveWireSerializer.machine.withEntry (0 : Fin 5)).run c bits) hp
    refine hr.trans ?_
    erw [KS.W29.BinaryMachine.withEntry_run, PositiveWireSerializer.run_num xs ys [] bits hbits]
    apply congrArg (KS.W29.Config.mk none)
    funext j
    fin_cases j <;> simp [wire]
  · intro j hj
    exact (registers_other ports spare _ _ _ j hj).trans
      (registers_other ports spare _ _ _ j hj).symm

theorem reverse_spec {k : ℕ} (ports : Fin 3 ↪ Fin k) (spare : Fin k → List Bool)
    (wire : List Bool) :
    RunSpec (reverseProgram ports) (registers ports spare [] [] wire.reverse)
      (registers ports spare [] wire []) (wire.length + 1) := by
  intro bits hbits
  change (lift3 KS.W29.NormalizeOutput.machine ports).run
    ⟨some (2 : Fin 3), registers ports spare [] [] wire.reverse⟩ bits = _
  apply lift3_run_eq
  · have hp : project ports
        (⟨some 2, registers ports spare [] [] wire.reverse⟩ : Config k 3) =
        KS.W29.FrameDecoder.config (some 2) [] [] wire.reverse := by
      apply congrArg (KS.W29.Config.mk (some (2 : Fin 3)))
      funext j
      fin_cases j <;> simp
    have hr := congrArg (fun c => KS.W29.NormalizeOutput.machine.run c bits) hp
    refine hr.trans ?_
    erw [KS.W29.NormalizeOutput.run_reversed [] wire bits hbits]
    apply congrArg (KS.W29.Config.mk none)
    funext j
    fin_cases j <;> simp
  · intro j hj
    exact (registers_other ports spare _ _ _ j hj).trans
      (registers_other ports spare _ _ _ j hj).symm

theorem serialize_spec {k : ℕ} (ports : Fin 3 ↪ Fin k) (spare : Fin k → List Bool)
    (xs ys : List Bool) :
    RunSpec (program ports) (registers ports spare xs ys [])
      (registers ports spare [] (wire xs ys) [])
      (4 * xs.length + 4 * ys.length + 5) := by
  have h := (emit_spec ports spare xs ys).compose
    (reverse_spec ports spare (wire xs ys))
  have ht : (2 * xs.length + 2 * ys.length + 2) +
      ((wire xs ys).length + 1) =
      4 * xs.length + 4 * ys.length + 5 := by
    rw [wire_length]
    omega
  rw [ht] at h
  exact h

end KS.W19.UnsignedPairSerializer

end OAI
