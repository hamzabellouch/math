import OAI.Combinatorics.ContingencyTables.Counting.CompanionMetropolisProgram
import OAI.Combinatorics.ContingencyTables.Counting.CompanionEvaluatedWeightLaw
import OAI.Combinatorics.ContingencyTables.Transport.FiniteMetropolisTransport
import OAI.Combinatorics.ContingencyTables.Rooted.RootedBooleanPhase

namespace OAI

/-! # The actual computed proposal and two oracle calls have the phase law -/

namespace ContingencyTables.CompanionMetropolisProgram

open MatchingFPRAS CompanionFactorialApplication CompanionComputedInitial CompanionComputedProposal
open CompanionBooleanPhase (State)
open CompanionArithmeticProposal CompanionOrderedProposal CompanionOracleDensity CompanionWeightOracle
open CompanionEvaluatedWeightProgram CompanionMultiplierMatrixProgram CommonBasesFPRAS
open FiniteObservableTransport TwoLiftStates GridBoundary
open scoped Classical
noncomputable section
variable {m n : ℕ}

abbrev Fields (A : Instance (Fin m) (Fin n)) (C K j k : ℕ) (xi : ℚ) :=
  (Fin 1 → Bool) × ((Fin (CompanionBooleanPhase.proposalBits A) → Bool) ×
    ((WeightWord A C K j xi × WeightWord A C K j xi) × (Fin k → Bool)))

def programInput (A : Instance (Fin m) (Fin n)) (C K j k : ℕ) (xi : ℚ)
    (cfg : RootedLabelWeightProgram.Config)
    (w : LabelIndex A → LabelIndex A → TreeFraction.Fraction)
    (S : State A) (b : Fields A C K j k xi) : Input :=
  (((cfg,matrixCode w),encodeSet (coordinateOrder A) S.val),
    (b.1 0,(List.ofFn b.2.1,((List.ofFn b.2.2.1.1,List.ofFn b.2.2.1.2),List.ofFn b.2.2.2))))

def codeAccept (A : Instance (Fin m) (Fin n)) (C K j k : ℕ) (xi : ℚ)
    (cfg : RootedLabelWeightProgram.Config)
    (w : LabelIndex A → LabelIndex A → TreeFraction.Fraction) (S T : State A)
    (b : (WeightWord A C K j xi × WeightWord A C K j xi) × (Fin k → Bool)) : Bool :=
  FractionMetropolisProgram.accept
    ((CompanionEvaluatedWeightProgram.output (((cfg,matrixCode w),encodeSet (coordinateOrder A) S.val),List.ofFn b.1.1),
      CompanionEvaluatedWeightProgram.output (((cfg,matrixCode w),encodeSet (coordinateOrder A) T.val),List.ofFn b.1.2)),
      List.ofFn b.2)

lemma output_programInput (A : Instance (Fin m) (Fin n)) (C K j k : ℕ) (xi : ℚ)
    (cfg : RootedLabelWeightProgram.Config)
    (w : LabelIndex A → LabelIndex A → TreeFraction.Fraction)
    (S : State A) (b : Fields A C K j k xi) :
    output (programInput A C K j k xi cfg w S b)=
      encodeSet (coordinateOrder A)
        (if b.1 0 then S else proposedMove S (orderedProposal A (coordinateOrder A) S b.2.1)
          (codeAccept A C K j k xi cfg w S) b.2.2).val := by
  cases hb : b.1 0 with
  | true => simp only [output,programInput,hb,ite_true]
  | false =>
    cases hp : orderedProposal A (coordinateOrder A) S b.2.1 with
    | none =>
      simp only [output,programInput,hb,Bool.false_eq_true,ite_false,accepted,acceptanceInput,
        currentValue,targetValue,currentInput,targetInput,candidate,proposed,
        CompanionComputedProposal.proposalProgram_eq,hp,Option.map_none,Option.getD_none,proposedMove]
      split_ifs <;> simp_all
    | some T =>
      simp only [output,programInput,hb,Bool.false_eq_true,ite_false,accepted,acceptanceInput,
        currentValue,targetValue,currentInput,targetInput,candidate,proposed,
        CompanionComputedProposal.proposalProgram_eq,hp,Option.map_some,Option.getD_some,proposedMove,
        codeAccept]
      split_ifs <;> simp_all

/-- Every computed step has the complete reference phase-step law. The
proposal and both query outcomes are transported, including failures. -/
theorem sameLaw_fields (A : Instance (Fin m) (Fin n)) (C K j k : ℕ)
    (hC : 0 < C) (hj : j ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=CompanionOracleDensity.binWidth A C)
    (xi : ℚ) (hxi : 0 < xi) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (degree depth : List Bool)
    (hdegree : degree.length=PowerOfTwoApproximation.rootDegree (roundingTolerance (innerTolerance (xi/2) j)))
    (hdepth : depth.length=PowerOfTwoApproximation.depth (roundingTolerance (innerTolerance (xi/2) j)))
    (w : LabelIndex A → LabelIndex A → TreeFraction.Fraction) (S : State A) :
    SameLaw (fun b : Fields A C K j k xi => output (programInput A C K j k xi
      (RootedLabelWeightProgram.config A C K j xi xi z v degree depth) w S b))
      (fun b : Fields A C K j k xi => encodeSet (coordinateOrder A)
        (RootedBooleanPhase.step A (RootedCompletion.rowColumn A.T) C K j k hK hW xi
          (RootedCatalogGrid.gridEquiv A K v) (sourceWeights A w) S
            ((CompanionBooleanPhase.stepWordEquiv A C K j k xi).symm b)).val) := by
  let cfg := RootedLabelWeightProgram.config A C K j xi xi z v degree depth
  let refAccept := fun T : State A => fun b :
      (WeightWord A C K j xi × WeightWord A C K j xi) × (Fin k → Bool) =>
    decide (FairBits.rationalThresholdAccept k
      (RootedOracleAcceptance.acceptance A (RootedCompletion.rowColumn A.T) C K j hK hW xi
        (RootedCatalogGrid.gridEquiv A K v) (sourceWeights A w) S.val T.val b.1) b.2)
  have hp : SameLaw (orderedProposal A (coordinateOrder A) S) (CompanionBooleanPhase.proposal A S) :=
    SameLaw.of_mapLaw_eq _ _ (orderedProposal_law A (coordinateOrder A) S)
  have ha (T : State A) : SameLaw (codeAccept A C K j k xi cfg w S T) (refAccept T) :=
    acceptance_sameLaw A C K j k hC hj hK hW hB xi hxi z v degree depth hdegree hdepth w S.val T.val
  have hm := proposedMove_sameLaw S _ _ _ _ hp ha
  have hh := (holding_sameLaw S _ _ hm).map (fun T : State A => encodeSet (coordinateOrder A) T.val)
  intro phi
  have hleft : (fun b : Fields A C K j k xi => phi (output (programInput A C K j k xi cfg w S b)))=
      (fun b : Fields A C K j k xi => phi (encodeSet (coordinateOrder A)
        (if b.1 0 then S else proposedMove S (orderedProposal A (coordinateOrder A) S b.2.1)
          (codeAccept A C K j k xi cfg w S) b.2.2).val)) := by
    funext b
    rw [output_programInput]
  rw [hleft]
  have he := hh phi
  refine he.trans ?_
  apply congrArg uniformAverage
  funext b
  apply congrArg phi
  unfold RootedBooleanPhase.step
  dsimp only
  simp only [Equiv.apply_symm_apply]
  cases hb : b.1 0 <;> cases hp : CompanionBooleanPhase.proposal A S b.2.1
  all_goals simp only [proposedMove,Bool.false_eq_true,ite_false,ite_true,refAccept,
    decide_eq_true_eq]

end
end ContingencyTables.CompanionMetropolisProgram

end OAI
