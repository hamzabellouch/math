import OAI.Combinatorics.ContingencyTables.Counting.CompanionCappedReturn
import OAI.Combinatorics.ContingencyTables.Counting.CompanionTraceProgram

namespace OAI

/-! # Binary program for a total capped return

The strict return scan is followed by the supplied initial code on a
missing return. Both operations have polynomial binary realizers.
-/

namespace ContingencyTables.CompanionCappedReturnProgram

open CommonBasesFPRAS MatchingFPRAS.TreeTyped ProfilePrograms
open CompanionFactorialApplication CompanionBooleanPhase CompanionChainValidator
open CompanionCappedReturn CompanionTraceProgram CompanionTraceWords CompanionPhaseTrajectory
open CompanionArithmeticProposal CompanionRationalUpdates GridBoundary
open scoped Classical

def optionDefault (z : List ℕ×Option (List ℕ)) : List ℕ := z.2.getD z.1

def optionDefaultRealizer : Realizer optionDefault :=
  (optionCases identity second).recode id optionDefault (fun _ => rfl)
    (by rintro ⟨d,o⟩; cases o <;> rfl)

theorem polynomial_optionDefault : PolynomialTime optionDefaultRealizer := by
  unfold optionDefaultRealizer
  apply polynomial_recode
  exact polynomial_optionCases polynomial_identity polynomial_second

abbrev TotalReturnInput := ReturnInput×List ℕ

def totalReturnCode (z : TotalReturnInput) : List ℕ :=
  (returnCode z.1).getD z.2

def totalReturnCodeRealizer : Realizer totalReturnCode :=
  composition (pair second (composition first returnCodeRealizer)) optionDefaultRealizer

theorem polynomial_totalReturnCode : PolynomialTime totalReturnCodeRealizer :=
  polynomial_composition (polynomial_pair polynomial_second
    (polynomial_composition polynomial_first polynomial_returnCode)) polynomial_optionDefault

noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]

/-- The binary result is the encoding of the same defaulted first return. -/
theorem totalReturnCode_encode (A : Instance I J)
    (S : PlainIndex (TwoLiftStates.pairs : List (Pair A))) (xs : List (State A)) :
    totalReturnCode ((pairCatalog A,xs.map (fun T => encodeSet (coordinateEquiv A) T.val)),
      encodeSet (coordinateEquiv A) S.val.val)=
      encodeSet (coordinateEquiv A)
        (returnDefault (plainPredicate TwoLiftStates.pairs) S xs).val.val := by
  unfold totalReturnCode
  rw [returnCode_encode]
  unfold returnDefault
  cases firstHit (plainPredicate TwoLiftStates.pairs) xs.tail <;> rfl

/-- In particular the program computes the literal finite-word return
experiment, not an independently specified trace sampler. -/
theorem totalReturnCode_recorded (A : Instance I J) (C K j k n : ℕ)
    (hK : 1≤K) (hW : 100*A.d*K≤A.W) (xi : ℚ)
    (v : Grid (I := Fin (CompanionOracleDensity.dimension A)) K)
    (w : Pair A → Pair A → ℚ)
    (S : PlainIndex (TwoLiftStates.pairs : List (Pair A)))
    (bits : Fin ((n+1)*stepBits A C K j k xi) → Bool) :
    totalReturnCode ((pairCatalog A,
      (historyPrefix (CompanionArithmeticStep.recordedWalk A C K j k (n+1) (n+1)
        hK hW xi v w S.val bits)).map (fun T => encodeSet (coordinateEquiv A) T.val)),
      encodeSet (coordinateEquiv A) S.val.val)=
      encodeSet (coordinateEquiv A)
        (returnWordDefault A C K j k n hK hW xi v w S bits).val.val := by
  exact totalReturnCode_encode A S _

end
end ContingencyTables.CompanionCappedReturnProgram

end OAI
