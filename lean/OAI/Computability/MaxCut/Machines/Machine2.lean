import Mathlib
import OAI.Computability.MaxCut.Encoding.FormulaEncoding

namespace OAI

namespace MaxCutGames.Foundations.Complexity

def naturalWordsEncoding : Computability.Encoding (List Nat) Bool where
  encode := encodeWords
  decode := decodeWords
  decode_encode := decodeWords_encodeWords

def formulaEncoding : Computability.Encoding Target.Formula Bool where
  encode := formulaBits
  decode := decodeFormulaBits
  decode_encode := decodeFormulaBits_encoded

/-- Concrete forward-table output syntax with a checked parser. -/
def gameEncoding (alphabet : Nat) : Computability.Encoding (Target.Instance alphabet) Bool where
  encode := gameBits
  decode := decodeGameBits alphabet
  decode_encode := decodeGameBits_encoded

/-- A fixed-bit prefixer uses one finite stack, one label, and one internal state.
The bit is fixed in the program; it is not a second, freely accessible input. -/
def prefixBitMachine (bit : Bool) : Turing.FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ _ := Bool
  Λ := Unit
  main := ()
  σ := Unit
  initialState := ()
  m _ := .push () (fun _ => bit) .halt

/-- A real machine certificate: one transition performs the push and halts.
TM2 counts execution of one finite statement as one transition. Here that
statement contains exactly one stack push. -/
noncomputable def prefixBitPolyTime (bit : Bool) :
    Turing.TM2ComputableInPolyTime (id : List Bool → List Bool) id (bit :: ·) where
  tm := prefixBitMachine bit
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 1
  outputsFun bs := {
    steps := 1
    evals_in_steps := by
      change some (Turing.TM2.stepAux (.push () (fun _ => bit) .halt) ()
          (fun _ : Unit => bs.map id)) =
        some { l := none, var := (), stk := fun _ : Unit => (bit :: bs).map id }
      simp [Turing.TM2.stepAux]
      funext k
      cases k
      rfl
    steps_le_m := by simp
  }

/-- Increasing a polynomial bound preserves the actual execution witness. -/
def enlargePolynomialBound {α β αΓ βΓ : Type}
    {ea : α → List αΓ} {eb : β → List βΓ} {f : α → β}
    (certificate : Turing.TM2ComputableInPolyTime ea eb f)
    (bound : Polynomial Nat)
    (larger : ∀ n, certificate.time.eval n ≤ bound.eval n) :
    Turing.TM2ComputableInPolyTime ea eb f where
  toTM2ComputableAux := certificate.toTM2ComputableAux
  time := bound
  outputsFun a := {
    toEvalsTo := (certificate.outputsFun a).toEvalsTo
    steps_le_m := Nat.le_trans (certificate.outputsFun a).steps_le_m (larger _)
  }

/-- Two verified phases of one transition system compose with added polynomial
budgets, both measured in the original input length. This theorem preserves the
actual sequence of transition steps, not merely the sizes of configurations. -/
def composeMachinePhases {σ : Type} (step : σ → Option σ)
    (start intermediate : σ) (finish : Option σ)
    (p q : Polynomial Nat) (inputLength : Nat)
    (first : StateTransition.EvalsToInTime step start (some intermediate) (p.eval inputLength))
    (second : StateTransition.EvalsToInTime step intermediate finish (q.eval inputLength)) :
    StateTransition.EvalsToInTime step start finish ((p + q).eval inputLength) := by
  have composed := StateTransition.EvalsToInTime.trans step (p.eval inputLength)
    (q.eval inputLength) start intermediate finish first second
  simpa only [Polynomial.eval_add, Nat.add_comm] using composed

open Target

structure PolynomialGapReduction
    (completenessError soundnessError : RationalError)
    extends SemanticGapReduction completenessError soundnessError where
  computation : Turing.TM2ComputableInPolyTime formulaEncoding.encode
    (gameEncoding alphabet).encode reduce

end MaxCutGames.Foundations.Complexity

end OAI
