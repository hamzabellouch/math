import OAI.Computability.UniqueGames.Machines.MachineFiniteAlphabet
import OAI.Computability.UniqueGames.Machines.MachineProductHeadersFrameLemmas
import OAI.Computability.UniqueGames.PCP.SourceRuntimeSpace

namespace OAI


/-! The complete explicit product computation. Every execution phase is supplied
by the actual controller; the cleanup bound follows from the space reached by
its actual prefix. The exponent and alphabet enter only the fixed program. -/

namespace UniqueGamesTheorem.Explicit.MachineProductRuntime

open Turing
open UniqueGamesTheorem.Foundations Target Complexity Hastad
open MachineProductProgram


noncomputable section

def loopPolynomial (q t : Nat) : Polynomial Nat :=
  (Polynomial.C (q ^ t + 2) * MachineProductBounds.fieldPolynomial t +
    Polynomial.C (2 * t)) * Polynomial.X ^ t

theorem loop_budget {q : Nat} (H : Instance q) (t : Nat) :
    (MachineProductLoop.bodyBound H t + 2 * t) * H.constraints.length ^ t ≤
      (loopPolynomial q t).eval (gameBits H).length := by
  have hlen := MachineProductLoop.input_length H
  have hm : H.constraints.length ≤ (gameBits H).length := by omega
  simp only [loopPolynomial, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hm t)

def prefixPolynomial (q t : Nat) : Polynomial Nat :=
  MachineProductHeaders.timePolynomial t + loopPolynomial q t

/-- Actual header initialization followed by every product row and odometer step. -/
def prefixInTime {q : Nat} (H : Instance q) (t : Nat) :
    StateTransition.EvalsToInTime (machine q t).step
      (initList (machine q t) (gameBits H))
      (some (MachineProductFinish.afterRows H t))
      ((prefixPolynomial q t).eval (gameBits H).length) := by
  let first := MachineProductHeaders.inPolynomialTime H t
  let loop := Classical.choice (MachineProductLoop.traversalInTime H
    (MachineProductHeaders.baseTapes H t) (MachineProductFinish.base_ready H t))
  let second : StateTransition.EvalsToInTime (machine q t).step
      (SourceOdometerSchedule.initialConfiguration (m := H.constraints.length)
        t (rowMain q t) ((), ()) (MachineProductHeaders.baseTapes H t))
      (some (MachineProductFinish.afterRows H t))
      ((loopPolynomial q t).eval (gameBits H).length) := {
    toEvalsTo := loop.toEvalsTo
    steps_le_m := loop.steps_le_m.trans (loop_budget H t) }
  let joined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first second
  exact {
    toEvalsTo := joined.toEvalsTo
    steps_le_m := by
      simpa only [prefixPolynomial, Polynomial.eval_add, Nat.add_comm]
        using joined.steps_le_m }

def timePolynomial (q t : Nat) : Polynomial Nat :=
  SourceRuntimeSpace.completedTime (machine q t) (clearKeys t).length
    (prefixPolynomial q t) + 1

/-- The complete run produces the literal full-table target code, clears all
private stacks, resets its finite state, and halts. -/
def outputInTime {q : Nat} (H : Instance q)
    (presentation : MachineOutputContract.SimpleBipartite H) (t : Nat) (ht : 0 < t) :
    TM2OutputsInTime (machine q t) (gameBits H)
      (some (gameBits (ProductPaddedOutput.output H presentation t ht)))
      ((timePolynomial q t).eval (gameBits H).length) := by
  let initialRun := prefixInTime H t
  let finish := Classical.choice (MachineProductFinish.finish_afterRows H presentation t ht)
  let whole := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ initialRun finish
  have keepAccumulator : accumulator t ∉ clearKeys t := by simp
  have keepOutput : output t ∉ clearKeys t := by simp
  have covers (k : Tape t) (ha : k ≠ accumulator t) (ho : k ≠ output t) :
      k ∈ clearKeys t := (mem_clearKeys t k).mpr ⟨ha, ho⟩
  have bound : SourceRuntimeFinish.finishCost (clearKeys t) (accumulator t)
      (MachineProductFinish.afterRows H t).stk ≤ (gameBits H).length +
        (prefixPolynomial q t).eval (gameBits H).length *
          (@Fintype.card (machine q t).K (machine q t).kFin * Runtime.programPushBound (machine q t)) +
        (clearKeys t).length + 2 :=
    SourceRuntimeSpace.finishCost_le_of_prefix (machine q t) (gameBits H)
    initialRun (clearKeys t) (accumulator t) (output t)
    keepAccumulator keepOutput covers
    (MachineProductFinish.afterRows H t).stk (MachineProductFinish.afterRows_output H t)
    (fun _ => rfl)
  change StateTransition.EvalsToInTime (machine q t).step _
    (some (haltList (machine q t) _)) _
  refine { toEvalsTo := whole.toEvalsTo, steps_le_m := whole.steps_le_m.trans ?_ }
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_one,
    SourceRuntimeSpace.completedTime_eval]
  omega

/-- The bipartition is proof-side data. Its codec is exactly the underlying
instance code and the fixed program does not inspect it. -/
abbrev Input (q : Nat) := Σ H : Instance q, MachineOutputContract.SimpleBipartite H

def construct {q : Nat} (t : Nat) (ht : 0 < t) (H : Input q) : Instance (q ^ t) :=
  ProductPaddedOutput.output H.1 H.2 t ht

def computation (q t : Nat) (ht : 0 < t) :
    TM2ComputableInPolyTime (fun H : Input q => gameBits H.1) gameBits
      (construct t ht) where
  tm := machine q t
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := timePolynomial q t
  outputsFun H := by
    change TM2OutputsInTime (machine q t) ((gameBits H.1).map id)
      (some ((gameBits (construct t ht H)).map id)) _
    have input_eq :
        @List.map ((machine q t).Γ (machine q t).k₀)
          ((machine q t).Γ (machine q t).k₀) id (gameBits H.1) = gameBits H.1 := List.map_id _
    have output_eq :
        @List.map ((machine q t).Γ (machine q t).k₁)
          ((machine q t).Γ (machine q t).k₁) id (gameBits (construct t ht H)) =
          gameBits (construct t ht H) := List.map_id _
    simpa only [input_eq, output_eq] using! outputInTime H.1 H.2 t ht

theorem finiteAlphabet (q t : Nat) (ht : 0 < t) :
    MachineFiniteAlphabet.FiniteAlphabet (computation q t ht).tm :=
  MachineFiniteAlphabet.of_bool _ (fun _ => rfl)

variable {A : Type} {q : Nat} {encode : A → List Bool} {f : A → Instance q}

def certify (upstream : TM2ComputableInPolyTime encode gameBits f)
    (presentation : ∀ a, MachineOutputContract.SimpleBipartite (f a)) :
    TM2ComputableInPolyTime encode (fun H : Input q => gameBits H.1)
      (fun a => ⟨f a, presentation a⟩) where
  tm := upstream.tm
  inputAlphabet := upstream.inputAlphabet
  outputAlphabet := upstream.outputAlphabet
  time := upstream.time
  outputsFun := upstream.outputsFun

/-- Direct composition with an actual preceding simple-bipartite producer. -/
def compose (upstream : TM2ComputableInPolyTime encode gameBits f)
    (presentation : ∀ a, MachineOutputContract.SimpleBipartite (f a))
    (t : Nat) (ht : 0 < t) :
    TM2ComputableInPolyTime encode gameBits
      (fun a => ProductPaddedOutput.output (f a) (presentation a) t ht) :=
  MachineSequential.composeBits (certify upstream presentation) (computation q t ht)

theorem compose_finiteAlphabet (upstream : TM2ComputableInPolyTime encode gameBits f)
    (presentation : ∀ a, MachineOutputContract.SimpleBipartite (f a))
    (t : Nat) (ht : 0 < t) (finite : MachineFiniteAlphabet.FiniteAlphabet upstream.tm) :
    MachineFiniteAlphabet.FiniteAlphabet (compose upstream presentation t ht).tm :=
  MachineFiniteAlphabet.composeBits (certify upstream presentation) (computation q t ht)
    finite (finiteAlphabet q t ht)

end

end UniqueGamesTheorem.Explicit.MachineProductRuntime

end OAI
