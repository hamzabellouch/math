import Mathlib
import OAI.Computability.MaxCut.PCP.PreprocessingRegularSoundness

namespace OAI

/-!
Verifier-defined NP over finite bitstring machines. This definition does not
mention SAT. Inputs and witnesses use a fixed explicit framing, verifiers return
one Boolean symbol, and all stacks have finite alphabets. The Cook–Levin target
separately requires an actual polynomial-time machine producing the established
`formulaBits` serialization, in addition to satisfiability equivalence.
-/

namespace MaxCutGames.Foundations.Complexity.CookLevin

/-- A unary length frame followed by input bits and witness bits. -/
def pairBits (input : List Bool × List Bool) : List Bool :=
  encodeWord input.1.length ++ input.1 ++ input.2

def decodePairAux : Nat → List Bool → Option (List Bool × List Bool)
  | _, [] => none
  | read, true :: rest => decodePairAux (read + 1) rest
  | read, false :: rest =>
      if read ≤ rest.length then some (rest.take read, rest.drop read) else none

def decodePair (bits : List Bool) : Option (List Bool × List Bool) :=
  decodePairAux 0 bits

theorem decodePairAux_frame (read count : Nat) (rest : List Bool) :
    decodePairAux read (List.replicate count true ++ false :: rest) =
      if read + count ≤ rest.length then
        some (rest.take (read + count), rest.drop (read + count)) else none := by
  induction count generalizing read with
  | zero => simp [decodePairAux]
  | succ count ih =>
    simp only [List.replicate_succ, List.cons_append, decodePairAux, ih]
    simp only [Nat.add_assoc, Nat.add_comm 1 count]

@[simp] theorem decodePair_pairBits (input : List Bool × List Bool) :
    decodePair (pairBits input) = some input := by
  rcases input with ⟨x, witness⟩
  simp [decodePair, pairBits, encodeWord, List.append_assoc,
    decodePairAux_frame]

theorem pairBits_injective : Function.Injective pairBits := by
  intro first second same
  have h := congrArg decodePair same
  simpa only [decodePair_pairBits, Option.some.injEq] using h

@[simp] theorem pairBits_length (input : List Bool × List Bool) :
    (pairBits input).length = 2 * input.1.length + input.2.length + 1 := by
  simp only [pairBits, List.length_append, encodeWord_length]
  omega

def pairEncoding : Computability.Encoding (List Bool × List Bool) Bool where
  encode := pairBits
  decode := decodePair
  decode_encode := decodePair_pairBits

/-- A standard polynomial-time Boolean verifier. `FinTM2` already requires
finitely many stacks, control labels, and internal states; this field also
requires every stack alphabet to be finite. The actual machine runs on the
explicit paired input and halts with exactly one Boolean output symbol. -/
structure NPVerifier where
  witnessBound : Polynomial Nat
  verify : (List Bool × List Bool) → Bool
  computation : Turing.TM2ComputableInPolyTime pairBits (fun bit => [bit]) verify
  finiteAlphabet : (k : computation.tm.K) → Fintype (computation.tm.Γ k)

def NPVerifier.Accepts (verifier : NPVerifier) (input : List Bool) : Prop :=
  ∃ witness : List Bool,
    witness.length ≤ verifier.witnessBound.eval input.length ∧
    verifier.verify (input, witness) = true

/-- NP is specified by polynomial witnesses and genuine finite-machine
verification, independently of any reduction or satisfiability problem. -/
def InNP (language : List Bool → Prop) : Prop :=
  ∃ verifier : NPVerifier, ∀ input, language input ↔ verifier.Accepts input

theorem NPVerifier.acceptedLanguage_inNP (verifier : NPVerifier) :
    InNP verifier.Accepts := ⟨verifier, fun _ => Iff.rfl⟩

/-- The demanded Cook–Levin endpoint: both the SAT equivalence and an actual
machine producing the fixed existing unary-token 3CNF encoding. This structure
contains obligations; its inhabitance is not assumed or asserted here. -/
structure PolynomialThreeSATReduction (language : List Bool → Prop) where
  reduce : List Bool → Target.Formula
  computation : Turing.TM2ComputableInPolyTime id formulaBits reduce
  correct : ∀ input, language input ↔ (reduce input).Satisfiable

/-- A common clock for all witnesses of permitted length for one input. -/
noncomputable def NPVerifier.horizon (verifier : NPVerifier) (inputLength : Nat) : Nat :=
  verifier.computation.time.eval
    (2 * inputLength + verifier.witnessBound.eval inputLength + 1)

theorem NPVerifier.input_time_le_horizon (verifier : NPVerifier)
    (input witness : List Bool)
    (bounded : witness.length ≤ verifier.witnessBound.eval input.length) :
    verifier.computation.time.eval (pairBits (input, witness)).length ≤
      verifier.horizon input.length := by
  apply MachineComposition.natPolynomial_eval_mono
  rw [pairBits_length]
  exact Nat.add_le_add_right (Nat.add_le_add_left bounded _) _

/-- A real verifier execution, enlarged to the single input-dependent clock.
The machine and its output are the ones supplied in the verifier definition. -/
def NPVerifier.runWithinHorizon (verifier : NPVerifier)
    (input witness : List Bool)
    (bounded : witness.length ≤ verifier.witnessBound.eval input.length) :
    Turing.TM2OutputsInTime verifier.computation.tm
      ((pairBits (input, witness)).map verifier.computation.inputAlphabet.invFun)
      (some ([verifier.verify (input, witness)].map verifier.computation.outputAlphabet.invFun))
      (verifier.horizon input.length) where
  toEvalsTo := (verifier.computation.outputsFun (input, witness)).toEvalsTo
  steps_le_m := Nat.le_trans
    (verifier.computation.outputsFun (input, witness)).steps_le_m
    (verifier.input_time_le_horizon input witness bounded)

end MaxCutGames.Foundations.Complexity.CookLevin

end OAI
