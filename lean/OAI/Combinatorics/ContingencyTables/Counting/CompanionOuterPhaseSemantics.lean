import OAI.Combinatorics.ContingencyTables.Counting.CompanionOuterPhaseProgram
import OAI.Combinatorics.ContingencyTables.Counting.CompanionPhaseTrialLaw
import OAI.Combinatorics.ContingencyTables.Counting.CompanionInitializedRestartJoint

namespace OAI

/-! # Literal data and slices of a complete adaptive phase -/
namespace ContingencyTables.CompanionOuterPhaseProgram
open MatchingFPRAS CommonBasesFPRAS CompanionFactorialApplication CompanionComputedInitial
open CompanionComputedProposal CompanionArithmeticProposal CompanionEvaluatedWeightProgram
open CompanionMultiplierMatrixProgram CompanionOracleDensity GridBoundary
open scoped BigOperators Classical
noncomputable section
variable {m n : ℕ}

def data (A : Instance (Fin m) (Fin n)) (C K H T N R L j : ℕ)
    (epsilon : TreeFraction.Fraction) (z : View A→ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (w : ℕ→LabelIndex A→LabelIndex A→TreeFraction.Fraction)
    (E : ℕ→TreeFraction.Fraction) (bits : List Bool) : Input :=
  (((CompanionRestartInitializer.data A C K H T N R L epsilon z v,(matrixCode (w 0),E 0)),
    List.ofFn (fun i : Fin j => (matrixCode (w (i.val+1)),E (i.val+1)))),bits)

lemma phase_data (A : Instance (Fin m) (Fin n)) (C K H T N R L j : ℕ)
    (epsilon : TreeFraction.Fraction) (z : View A→ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (w : ℕ→LabelIndex A→LabelIndex A→TreeFraction.Fraction)
    (E : ℕ→TreeFraction.Fraction) (bits : List Bool) :
    phase (data A C K H T N R L j epsilon z v w E bits)=j := by
  simp only [phase,history,data,List.length_ofFn]

lemma old_data (A : Instance (Fin m) (Fin n)) (C K H T N R L j : ℕ)
    (epsilon : TreeFraction.Fraction) (z : View A→ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (w : ℕ→LabelIndex A→LabelIndex A→TreeFraction.Fraction)
    (E : ℕ→TreeFraction.Fraction) (bits : List Bool) :
    old (data A C K H T N R L j epsilon z v w E bits)=(matrixCode (w j),E j) := by
  rw [old,phase_data]
  cases j with
  | zero => rfl
  | succ j =>
    simp only [Nat.add_one_ne_zero,ite_false,history,data,Nat.add_sub_cancel,
      List.getD_eq_getElem?_getD,List.getElem?_ofFn,Nat.lt_succ_self,dite_true,Option.getD_some]

lemma restartInput_data (A : Instance (Fin m) (Fin n)) (C K H T N R L j : ℕ)
    (epsilon : TreeFraction.Fraction) (z : View A→ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (w : ℕ→LabelIndex A→LabelIndex A→TreeFraction.Fraction)
    (E : ℕ→TreeFraction.Fraction) (bits : List Bool) :
    restartInput (data A C K H T N R L j epsilon z v w E bits)=
      CompanionInitializedRestartProgram.data A C K H T N R L j epsilon z v w
        (fun i => E (i.val+1)) bits := rfl

lemma configAt_data (A : Instance (Fin m) (Fin n)) (C K H T N R L j i : ℕ)
    (epsilon : TreeFraction.Fraction) (z : View A→ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (w : ℕ→LabelIndex A→LabelIndex A→TreeFraction.Fraction)
    (E : ℕ→TreeFraction.Fraction) (bits : List Bool) :
    configAt i (data A C K H T N R L j epsilon z v w E bits)=
      RootedLabelWeightProgram.config A C K (j+i)
        (TreeFraction.val (CountingPhaseParametersProgram.noise
          (CompanionInitializedRestartProgram.parameters A H T N R L epsilon)))
        (TreeFraction.val (CountingPhaseParametersProgram.noise
          (CompanionInitializedRestartProgram.parameters A H T N R L epsilon))) z v
        (CompanionRestartStageProgram.degree A C K (j+i)
          (CompanionInitializedRestartProgram.parameters A H T N R L epsilon) z v bits)
        (CompanionRestartStageProgram.depth A C K (j+i)
          (CompanionInitializedRestartProgram.parameters A H T N R L epsilon) z v bits) := by
  unfold configAt contextInput
  rw [phase_data]
  change CompanionPhaseContextProgram.config (CompanionPhaseContextProgram.data A C K (j+i)
    (CompanionInitializedRestartProgram.parameters A H T N R L epsilon) z v (reserve _))=_
  rw [CompanionPhaseContextProgram.config_data,RootedOracleConfigProgram.output_data]
  simp only [reserve,data,List.map_const',List.length_replicate,
    CompanionRestartStageProgram.degree,CompanionRestartStageProgram.depth,
    CompanionRestartStageProgram.oracleData]



lemma restartWidth_data (A : Instance (Fin m) (Fin n)) (C K H T N R L j : ℕ)
    (epsilon : TreeFraction.Fraction) (z : View A→ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (w : ℕ→LabelIndex A→LabelIndex A→TreeFraction.Fraction)
    (E : ℕ→TreeFraction.Fraction) (bits : List Bool) :
    restartWidth (data A C K H T N R L j epsilon z v w E bits)=
      wordLength A (CompanionInitialDraw.precision A (CountingPhaseSchedule.initialPrecision H))+
        CompanionRestartProgram.sumBits A C K j
          (CompanionInitializedRestartProgram.parameters A H T N R L epsilon) := by
  unfold restartWidth restartRequest
  change CompanionRestartSchedule.width (CompanionRestartInitializer.data A C K H T N R L epsilon z v,_)=_
  rw [CompanionRestartSchedule.width,CompanionRestartInitializer.width_data,
    CompanionRestartSchedule.restartWidth_data]
  rw [show (history (data A C K H T N R L j epsilon z v w E bits)).length=j from
    phase_data A C K H T N R L j epsilon z v w E bits]
  rfl

lemma walkState_data (A : Instance (Fin m) (Fin n)) (C K H T N R L j : ℕ)
    (epsilon : TreeFraction.Fraction) (z : View A→ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (w : ℕ→LabelIndex A→LabelIndex A→TreeFraction.Fraction)
    (E : ℕ→TreeFraction.Fraction) (bits : List Bool) (S : CompanionBooleanPhase.State A)
    (hs : startCode (data A C K H T N R L j epsilon z v w E bits)=encodeSet (coordinateOrder A) S.val) :
    walkState (data A C K H T N R L j epsilon z v w E bits)=
      CompanionFlatReturnProgram.stateData A C K j
        (CountingPhaseParametersProgram.precision (CompanionInitializedRestartProgram.parameters A H T N R L epsilon))
        (TreeFraction.val (CountingPhaseParametersProgram.noise (CompanionInitializedRestartProgram.parameters A H T N R L epsilon)))
        z v
        (CompanionRestartStageProgram.degree A C K j (CompanionInitializedRestartProgram.parameters A H T N R L epsilon) z v bits)
        (CompanionRestartStageProgram.depth A C K j (CompanionInitializedRestartProgram.parameters A H T N R L epsilon) z v bits)
        (w j) S := by
  unfold walkState
  rw [configAt_data,old_data,hs]
  simp only [Nat.add_zero]
  rfl

lemma trajectoryWidth_data (A : Instance (Fin m) (Fin n)) (C K H T N R L j : ℕ)
    (epsilon : TreeFraction.Fraction) (z : View A→ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (w : ℕ→LabelIndex A→LabelIndex A→TreeFraction.Fraction)
    (E : ℕ→TreeFraction.Fraction) (bits : List Bool) (S : CompanionBooleanPhase.State A)
    (hs : startCode (data A C K H T N R L j epsilon z v w E bits)=encodeSet (coordinateOrder A) S.val) :
    trajectoryWidth (data A C K H T N R L j epsilon z v w E bits)=
      CountingPhaseParametersProgram.observations (CompanionInitializedRestartProgram.parameters A H T N R L epsilon)*
        CompanionBooleanPhase.stepBits A C K j
          (CountingPhaseParametersProgram.precision (CompanionInitializedRestartProgram.parameters A H T N R L epsilon))
          (TreeFraction.val (CountingPhaseParametersProgram.noise (CompanionInitializedRestartProgram.parameters A H T N R L epsilon))) := by
  unfold trajectoryWidth widthInput
  rw [walkState_data A C K H T N R L j epsilon z v w E bits S hs]
  change CountingPhaseParametersProgram.observations _*
    CompanionTransitionWidth.width (CompanionMetropolisWordProgram.packed
      (RootedLabelWeightProgram.config A C K j _ _ z v _ _,matrixCode (w j)) _
      (encodeSet (coordinateOrder A) S.val) [])=_
  rw [CompanionTransitionWidth.width_config]
  rfl



lemma trialInput_data (A : Instance (Fin m) (Fin n)) (C K H T N R L j : ℕ)
    (epsilon : TreeFraction.Fraction) (z : View A→ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (w : ℕ→LabelIndex A→LabelIndex A→TreeFraction.Fraction)
    (E : ℕ→TreeFraction.Fraction) (bits : List Bool) (S : CompanionBooleanPhase.State A)
    (hs : startCode (data A C K H T N R L j epsilon z v w E bits)=encodeSet (coordinateOrder A) S.val) :
    let p := CompanionInitializedRestartProgram.parameters A H T N R L epsilon
    let xi := TreeFraction.val (CountingPhaseParametersProgram.noise p)
    let k := CountingPhaseParametersProgram.precision p
    let obs := CountingPhaseParametersProgram.observations p
    let a := wordLength A (CompanionInitialDraw.precision A (CountingPhaseSchedule.initialPrecision H))+
      CompanionRestartProgram.sumBits A C K j p
    let t := obs*CompanionBooleanPhase.stepBits A C K j k xi
    trialInput (data A C K H T N R L j epsilon z v w E bits)=
      CompanionPhaseTrialProgram.data A C K j k obs xi z v
        (CompanionRestartStageProgram.degree A C K j p z v bits)
        (CompanionRestartStageProgram.depth A C K j p z v bits)
        (CompanionRestartStageProgram.degree A C K (j+1) p z v bits)
        (CompanionRestartStageProgram.depth A C K (j+1) p z v bits)
        (w j) (E j) S ((bits.drop a).take t) ((bits.drop a).drop t) := by
  dsimp only
  unfold trialInput trajectoryInput
  rw [configAt_data,configAt_data,old_data,
    walkState_data A C K H T N R L j epsilon z v w E bits S hs,
    trajectoryWidth_data A C K H T N R L j epsilon z v w E bits S hs]
  unfold afterRestart
  rw [restartWidth_data]
  simp only [Nat.add_zero]
  rfl

end
end ContingencyTables.CompanionOuterPhaseProgram

end OAI
