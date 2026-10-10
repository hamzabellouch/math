import OAI.Combinatorics.ContingencyTables.Counting.CompanionPhaseTrialProgram
import OAI.Combinatorics.ContingencyTables.Counting.CompanionTrajectoryLaw
import OAI.Combinatorics.ContingencyTables.Counting.CompanionObservedUpdateLaw
import OAI.Combinatorics.ContingencyTables.Machines.FiniteEncodedBind
import OAI.Combinatorics.ContingencyTables.Rooted.RootedPhaseTrial
import OAI.Combinatorics.ContingencyTables.Rooted.RootedRestartAgreement

namespace OAI

/-! # The executed trajectory and fresh queries form the source phase trial -/
namespace ContingencyTables.CompanionPhaseTrialProgram
open MatchingFPRAS CommonBasesFPRAS CompanionFactorialApplication CompanionComputedInitial
open CompanionComputedProposal CompanionOrderedProposal CompanionArithmeticProposal
open CompanionOracleDensity CompanionWeightOracle CompanionMultiplierMatrixProgram
open CompanionEvaluatedWeightProgram FiniteObservableTransport GridBoundary TwoLiftStates
open scoped Classical
noncomputable section
variable {m n : ℕ}

def data (A : Instance (Fin m) (Fin n)) (C K j k N : ℕ) (xi : ℚ)
    (z : View A→ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (degree depth nextDegree nextDepth : List Bool)
    (w : LabelIndex A→LabelIndex A→TreeFraction.Fraction) (E : TreeFraction.Fraction)
    (S : CompanionBooleanPhase.State A) (walkBits queryBits : List Bool) : Input :=
  (((CompanionObservationQueriesProgram.phaseConfigs A C K j xi z v degree depth nextDegree nextDepth,
      (matrixCode w,E)),
    CompanionFlatReturnProgram.data A C K j k N xi z v degree depth w S walkBits),queryBits)

lemma output_data (A : Instance (Fin m) (Fin n)) (C K j k N : ℕ) (xi : ℚ)
    (z : View A→ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (degree depth nextDegree nextDepth : List Bool)
    (w : LabelIndex A→LabelIndex A→TreeFraction.Fraction) (E : TreeFraction.Fraction)
    (S : CompanionBooleanPhase.State A) (walkBits queryBits : List Bool) :
    output (data A C K j k N xi z v degree depth nextDegree nextDepth w E S walkBits queryBits)=
      CompanionObservedUpdateProgram.output
        ((CompanionObservationQueriesProgram.phaseConfigs A C K j xi z v degree depth nextDegree nextDepth,
          (((orderedCatalog A (pairLabels A) (coordinateOrder A),
            CompanionTrajectoryProgram.output
              (CompanionFlatReturnProgram.data A C K j k N xi z v degree depth w S walkBits)),
            matrixCode w),E)),queryBits) := by
  simp only [output,updateInput,storedInput,returnInput,catalogue,trajectory,data,
    CompanionFlatReturnProgram.data,CompanionFlatReturnProgram.stateData]
  rw [generated_catalog]

/-- Before changing multiplier representation, this law uses the canonical
matrix's source weights for the trajectory and the given stored value for the update. -/
theorem sameLaw (A : Instance (Fin m) (Fin n)) (C K j k N : ℕ)
    (hC : 0<C) (hj : j+1 ≤ rationalHeight A C) (hK : 1≤K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C)
    (xi : ℚ) (hxi : 0<xi) (z : View A→ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (degree depth nextDegree nextDepth : List Bool)
    (hdegree : degree.length=PowerOfTwoApproximation.rootDegree (roundingTolerance (innerTolerance (xi/2) j)))
    (hdepth : depth.length=PowerOfTwoApproximation.depth (roundingTolerance (innerTolerance (xi/2) j)))
    (hnextDegree : nextDegree.length=PowerOfTwoApproximation.rootDegree (roundingTolerance (innerTolerance (xi/2) (j+1))))
    (hnextDepth : nextDepth.length=PowerOfTwoApproximation.depth (roundingTolerance (innerTolerance (xi/2) (j+1))))
    (old : CompanionPhaseWords.Stored A)
    (w : LabelIndex A→LabelIndex A→TreeFraction.Fraction) (E : TreeFraction.Fraction)
    (hw : ∀ i j,TreeFraction.val (w i j)=old.multiplier (pair (pairLabels A i)) (pair (pairLabels A j)))
    (hE : TreeFraction.val E=old.estimate) (S : CompanionBooleanPhase.State A) :
    let cs := CompanionObservationQueriesProgram.phaseConfigs A C K j xi z v degree depth nextDegree nextDepth
    SameLaw (fun bits : (Fin (N*CompanionBooleanPhase.stepBits A C K j k xi)→Bool) ×
        (Fin ((N+1)*CompanionObservationQueriesProgram.blockWidth cs)→Bool) =>
      (output (data A C K j k N xi z v degree depth nextDegree nextDepth w E S
        (List.ofFn bits.1) (List.ofFn bits.2))).map (CompanionPhaseFinishProgram.view (p := (CanonicalInitialEncoding.copyOrder (capacities A)).length)))
      (fun bits : RootedPhaseTrial.TrialWords A C K j k N xi =>
        (RootedPhaseWords.update A (RootedCompletion.rowColumn A.T) C K j (N+1) hK hW xi
          (RootedCatalogGrid.gridEquiv A K v) old
          (RootedPhaseExperiment.observedStates A (RootedCompletion.rowColumn A.T)
            C K j k N hK hW xi (RootedCatalogGrid.gridEquiv A K v) (sourceWeights A w) S bits.1)
          bits.2).map (CompanionPhaseFinishProgram.storedView A (pairLabels A))) := by
  dsimp only
  let cs := CompanionObservationQueriesProgram.phaseConfigs A C K j xi z v degree depth nextDegree nextDepth
  let f := fun bits : Fin (N*CompanionBooleanPhase.stepBits A C K j k xi)→Bool =>
    CompanionTrajectoryProgram.output
      (CompanionFlatReturnProgram.data A C K j k N xi z v degree depth w S (List.ofFn bits))
  let g := RootedPhaseExperiment.observedStates A (RootedCompletion.rowColumn A.T)
    C K j k N hK hW xi (RootedCatalogGrid.gridEquiv A K v) (sourceWeights A w) S
  let e := fun states : Fin (N+1)→Set (Labels A×Bool) =>
    (List.ofFn states).map (encodeSet (coordinateOrder A))
  let F := fun codes : List (List ℕ) => fun bits : Fin ((N+1)*CompanionObservationQueriesProgram.blockWidth cs)→Bool =>
    (CompanionObservedUpdateProgram.output
      ((cs,(((orderedCatalog A (pairLabels A) (coordinateOrder A),codes),matrixCode w),E)),
        List.ofFn bits)).map (CompanionPhaseFinishProgram.view (p := (CanonicalInitialEncoding.copyOrder (capacities A)).length))
  let G := fun states : Fin (N+1)→Set (Labels A×Bool) =>
    fun bits : Fin (CompanionPhaseWords.phaseBits A C K j (N+1) xi)→Bool =>
      (RootedPhaseWords.update A (RootedCompletion.rowColumn A.T) C K j (N+1) hK hW xi
        (RootedCatalogGrid.gridEquiv A K v) old states bits).map
          (CompanionPhaseFinishProgram.storedView A (pairLabels A))
  have hi : SameLaw f (fun bits => e (g bits)) :=
    CompanionTrajectoryProgram.observations_sameLaw A C K j k N hC (by omega) hK hW hB
      xi hxi z v degree depth hdegree hdepth w S
  have hs : ∀ states,SameLaw (F (e states)) (G states) := by
    intro states
    exact CompanionObservedUpdateProgram.sameLaw_phase A C K j hC hj hK hW hB xi hxi z v
      degree depth nextDegree nextDepth hdegree hdepth hnextDegree hnextDepth states old w E hw hE
  have h := encoded_bind f g e F G hi hs
  intro phi
  have hl : (fun bits : (Fin (N*CompanionBooleanPhase.stepBits A C K j k xi)→Bool) ×
      (Fin ((N+1)*CompanionObservationQueriesProgram.blockWidth cs)→Bool) => phi ((output (data A C K j k N xi z v degree depth nextDegree nextDepth
      w E S (List.ofFn bits.1) (List.ofFn bits.2))).map (CompanionPhaseFinishProgram.view (p := (CanonicalInitialEncoding.copyOrder (capacities A)).length))))=
      (fun bits => phi (F (f bits.1) bits.2)) := by
    funext bits
    rw [output_data]
  rw [hl]
  exact h phi

theorem trial_sameLaw (A : Instance (Fin m) (Fin n)) (C K j k N : ℕ)
    (hC : 0<C) (hj : j+1 ≤ rationalHeight A C) (hK : 1≤K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C)
    (xi : ℚ) (hxi : 0<xi) (z : View A→ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (degree depth nextDegree nextDepth : List Bool)
    (hdegree : degree.length=PowerOfTwoApproximation.rootDegree (roundingTolerance (innerTolerance (xi/2) j)))
    (hdepth : depth.length=PowerOfTwoApproximation.depth (roundingTolerance (innerTolerance (xi/2) j)))
    (hnextDegree : nextDegree.length=PowerOfTwoApproximation.rootDegree (roundingTolerance (innerTolerance (xi/2) (j+1))))
    (hnextDepth : nextDepth.length=PowerOfTwoApproximation.depth (roundingTolerance (innerTolerance (xi/2) (j+1))))
    (old : CompanionPhaseWords.Stored A)
    (w : LabelIndex A→LabelIndex A→TreeFraction.Fraction) (E : TreeFraction.Fraction)
    (hw : ∀ i j,TreeFraction.val (w i j)=old.multiplier (pair (pairLabels A i)) (pair (pairLabels A j)))
    (hE : TreeFraction.val E=old.estimate) (S : CompanionBooleanPhase.State A) :
    let cs := CompanionObservationQueriesProgram.phaseConfigs A C K j xi z v degree depth nextDegree nextDepth
    SameLaw (fun bits : (Fin (N*CompanionBooleanPhase.stepBits A C K j k xi)→Bool) ×
        (Fin ((N+1)*CompanionObservationQueriesProgram.blockWidth cs)→Bool) =>
      (output (data A C K j k N xi z v degree depth nextDegree nextDepth w E S
        (List.ofFn bits.1) (List.ofFn bits.2))).map (CompanionPhaseFinishProgram.view (p := (CanonicalInitialEncoding.copyOrder (capacities A)).length)))
      (fun bits : RootedPhaseTrial.TrialWords A C K j k N xi =>
        (RootedPhaseTrial.trial A (RootedCompletion.rowColumn A.T) C K j k N hK hW xi
          (RootedCatalogGrid.gridEquiv A K v) old S bits).map
            (CompanionPhaseFinishProgram.storedView A (pairLabels A))) := by
  have hag : CompanionMultiplierAgreement.Agree A (sourceWeights A w) old.multiplier := by
    intro a b
    simpa only [sourceWeights,pair,Equiv.apply_symm_apply] using
      hw ((pairLabels A).symm a) ((pairLabels A).symm b)
  have h := sameLaw A C K j k N hC hj hK hW hB xi hxi z v degree depth nextDegree nextDepth
    hdegree hdepth hnextDegree hnextDepth old w E hw hE S
  dsimp only at h ⊢
  rw [CompanionMultiplierAgreement.observedStates_eq A (RootedCompletion.rowColumn A.T)
    C K j k N hK hW xi (RootedCatalogGrid.gridEquiv A K v) (sourceWeights A w) old.multiplier hag] at h
  exact h

end
end ContingencyTables.CompanionPhaseTrialProgram

end OAI
