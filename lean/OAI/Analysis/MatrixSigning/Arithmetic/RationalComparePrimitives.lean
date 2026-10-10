import Mathlib
import OAI.Analysis.MatrixSigning.Machines.FixedPortRunSpec
import OAI.Analysis.MatrixSigning.Arithmetic.MultiplicationLoop
import OAI.Analysis.MatrixSigning.Arithmetic.MultiplicationNormalize

namespace OAI

section

namespace KS.W06.RationalCompare

open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def replacePorts {k K : ℕ} (ports : Fin k ↪ Fin K)
    (before : Fin K → List Bool) (after : Fin k → List Bool) : Fin K → List Bool :=
  fun j => match portPreimage ports j with
    | none => before j
    | some i => after i

@[simp] theorem replacePorts_on {k K : ℕ} (ports : Fin k ↪ Fin K)
    (before : Fin K → List Bool) (after : Fin k → List Bool) (i : Fin k) :
    replacePorts ports before after (ports i) = after i := by
  simp [replacePorts]

theorem replacePorts_off {k K : ℕ} (ports : Fin k ↪ Fin K)
    (before : Fin K → List Bool) (after : Fin k → List Bool) (j : Fin K)
    (hj : ∀ i, j ≠ ports i) : replacePorts ports before after j = before j := by
  simp [replacePorts, portPreimage_off_port ports j hj]

theorem runSpec_liftPorts {k K : ℕ} (P : Program k) (ports : Fin k ↪ Fin K)
    (before : Fin K → List Bool) (after : Fin k → List Bool) (ticks : ℕ)
    (h : RunSpec P (fun i => before (ports i)) after ticks) :
    RunSpec (KS.W29.FixedSequential.liftPorts P ports) before
      (replacePorts ports before after) ticks := by
  apply KS.W01.FixedPortRunSpec.lift_runSpec P ports
    (fun i => before (ports i)) after before
    (replacePorts ports before after) ticks h
  · intro i; rfl
  · intro i; exact replacePorts_on ports before after i
  · intro j hj; exact replacePorts_off ports before after j hj

def replace3 {k : ℕ} (ports : Fin 3 ↪ Fin k) (before : Fin k → List Bool)
    (a b c : List Bool) : Fin k → List Bool := fun j =>
  if j = ports 0 then a else if j = ports 1 then b else if j = ports 2 then c else before j

@[simp] theorem replace3_on {k : ℕ} (ports : Fin 3 ↪ Fin k) (before : Fin k → List Bool)
    (a b c : List Bool) (i : Fin 3) : replace3 ports before a b c (ports i) = ![a,b,c] i := by
  fin_cases i <;> simp [replace3, ports.injective.eq_iff]

def decodeProgram {k : ℕ} (ports : Fin 3 ↪ Fin k) : Program k :=
  ofMachine (lift3 KS.W29.FrameDecoder.machine ports)

theorem decode_spec {k : ℕ} (ports : Fin 3 ↪ Fin k) (before : Fin k → List Bool)
    (payload tail : List Bool)
    (hin : before (ports 0) = KS.W01.frame payload ++ tail)
    (hout : before (ports 1) = []) (hscratch : before (ports 2) = []) :
    RunSpec (decodeProgram ports) before (replace3 ports before tail payload [])
      (3 * payload.length + 2) := by
  intro bits hbits
  change (lift3 KS.W29.FrameDecoder.machine ports).run ⟨some (0 : Fin 3), before⟩ bits = _
  apply lift3_run_eq
  · have hp : project ports (⟨some 0, before⟩ : Config k 3) =
        KS.W29.FrameDecoder.machine.init (KS.W01.frame payload ++ tail) := by
      change KS.W29.Config.mk (some (0 : Fin 3)) _ = KS.W29.Config.mk (some (0 : Fin 3)) _
      apply congrArg (KS.W29.Config.mk (some (0 : Fin 3)))
      funext i
      fin_cases i <;> simp [hin, hout, hscratch]
    erw [hp, KS.W29.FrameDecoder.run_frame payload tail bits hbits]
    apply congrArg (KS.W29.Config.mk none)
    funext i
    fin_cases i <;> simp
  · intro j hj
    simp [replace3, hj 0, hj 1, hj 2]

def signDispatch {k : ℕ} (source target : Fin k) (_ : Fin 1)
    (heads : Fin k → Fin 3) (_ : Bool) : Instruction k 1 :=
  ⟨none, Vector.ofFn (fun j => if j = source then .pop
    else if j = target then .push ((heads source).val == 2) else .stay)⟩

def signProgram {k : ℕ} (source target : Fin k) : Program k :=
  ofMachine (compile (0 : Fin 1) source target (signDispatch source target))

def signAfter {k : ℕ} (source target : Fin k) (before : Fin k → List Bool)
    (sign : Bool) (tail : List Bool) : Fin k → List Bool := fun j =>
  if j = source then tail else if j = target then sign :: before j else before j

theorem sign_spec {k : ℕ} (source target : Fin k) (hst : source ≠ target)
    (before : Fin k → List Bool) (sign : Bool) (tail : List Bool)
    (hin : before source = sign :: tail) :
    RunSpec (signProgram source target) before (signAfter source target before sign tail) 1 := by
  intro bits hbits
  cases bits with
  | nil => simp at hbits
  | cons coin rest =>
      have hr : rest = [] := List.length_eq_zero_iff.mp (by simpa using hbits)
      subst rest
      change (compile (0 : Fin 1) source target (signDispatch source target)).step
        ⟨some (0 : Fin 1), before⟩ coin = _
      rw [step_compile]
      apply congrArg (Config.mk none)
      funext j
      by_cases hjs : j = source
      · subst j
        simp [signDispatch, Instruction.action, signAfter, hin, KS.W29.StackAction.apply]
      · by_cases hjt : j = target
        · subst j
          cases sign <;> simp [signDispatch, Instruction.action, signAfter, hin,
            Ne.symm hst, observedHeads, KS.W29.topCode, KS.W29.StackAction.apply]
        · simp [signDispatch, Instruction.action, signAfter, hjs, hjt, KS.W29.StackAction.apply]

def productProgram : Program 7 :=
  compose KS.W03.MultiplicationLoop.program KS.W03.MultiplicationNormalize.program

def productTicks (xs ys : List Bool) : ℕ :=
  KS.W03.BinaryAccumulator.loopTicks xs ys [] +
    (2 * (KS.W03.BinaryAccumulator.loop xs ys []).length + 2)

theorem product_spec (input xs ys : List Bool) :
    RunSpec productProgram (KS.W03.MultiplicationBody.registers input xs ys [] [] [] [])
      (KS.W03.MultiplicationBody.registers input [] (KS.W03.MultiplicationLoop.advance xs ys)
        (Computability.encodeNat (KS.W19.bitsValue xs * KS.W19.bitsValue ys)) [] [] [])
      (productTicks xs ys) := by
  have h := (KS.W03.MultiplicationLoop.loop_spec input xs ys []).compose
    (KS.W03.MultiplicationNormalize.normalize_spec input []
      (KS.W03.MultiplicationLoop.advance xs ys) (KS.W03.BinaryAccumulator.loop xs ys []))
  rw [KS.W03.BinaryAccumulator.loop_zero_correct] at h
  exact h

theorem productTicks_le (xs ys : List Bool) :
    productTicks xs ys ≤ 16 * (xs.length + ys.length + 2) ^ 2 := by
  have ht := KS.W03.BinaryAccumulator.loop_zero_ticks_le xs ys
  have hl := KS.W03.BinaryAccumulator.loop_zero_length_le xs ys
  unfold productTicks
  nlinarith [Nat.zero_le ((xs.length + ys.length) * (xs.length + ys.length))]

end KS.W06.RationalCompare

end

end OAI
