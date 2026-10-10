import OAI.Combinatorics.ContingencyTables.Counting.CompanionOuterPhaseSemantics
import OAI.Combinatorics.ContingencyTables.Counting.CompanionTrialPadding

namespace OAI

/-! # Continuing an adaptive phase from its initialized profile -/
namespace ContingencyTables.CompanionPhaseContinuation
open MatchingFPRAS CompanionFactorialApplication CompanionComputedInitial CompanionComputedProposal
open CompanionArithmeticProposal CompanionEvaluatedWeightProgram CompanionMultiplierMatrixProgram
open CompanionOracleDensity CompanionWeightOracle GridBoundary FiniteObservableTransport CommonBasesFPRAS TwoLiftStates
open scoped Classical
noncomputable section

abbrev Configs := CompanionObservedUpdateProgram.Configs
abbrev Stored := CompanionPhaseFinishProgram.Stored

def state (cs : Configs) (old : Stored) (k : ℕ) (code : List ℕ) : CompanionBoundedWalkProgram.State :=
  ((((cs.1,old.1),k),code),code)

def width (cs : Configs) (old : Stored) (k : ℕ) (code : List ℕ) : ℕ :=
  CompanionTransitionWidth.width ((((cs.1,old.1),k),code),[])

def input (cs : Configs) (old : Stored) (k N : ℕ) (code : List ℕ) (tail : List Bool) :
    CompanionPhaseTrialProgram.Input :=
  (((cs,old),((state cs old k code,N),tail.take (N*width cs old k code))),
    tail.drop (N*width cs old k code))

def run (cs : Configs) (old : Stored) (k N : ℕ) (code : List ℕ) (tail : List Bool) : Stored :=
  (CompanionPhaseTrialProgram.output (input cs old k N code tail)).getD old

lemma outer_eq (z : CompanionOuterPhaseProgram.Input) :
    CompanionOuterPhaseProgram.output z=
      run (CompanionOuterPhaseProgram.configAt 0 z,CompanionOuterPhaseProgram.configAt 1 z)
        (CompanionOuterPhaseProgram.old z) (CompanionOuterPhaseProgram.precision z)
        (CompanionOuterPhaseProgram.observations z) (CompanionOuterPhaseProgram.startCode z)
        (CompanionOuterPhaseProgram.afterRestart z) := rfl

lemma view_getD {p : ℕ} (o : Option Stored) (s : Stored) :
    CompanionPhaseFinishProgram.view (p := p) (o.getD s)=
      (o.map CompanionPhaseFinishProgram.view).getD (CompanionPhaseFinishProgram.view s) := by
  cases o <;> rfl

variable {m n : ℕ}

lemma input_encoded (A : Instance (Fin m) (Fin n)) (C K j k N : ℕ) (xi : ℚ)
    (z : View A→ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (degree depth nextDegree nextDepth : List Bool)
    (w : LabelIndex A→LabelIndex A→TreeFraction.Fraction) (E : TreeFraction.Fraction)
    (S : CompanionBooleanPhase.State A) (tail : List Bool) :
    let cs := CompanionObservationQueriesProgram.phaseConfigs A C K j xi z v degree depth nextDegree nextDepth
    input cs (matrixCode w,E) k N (encodeSet (coordinateOrder A) S.val) tail=
      CompanionPhaseTrialProgram.data A C K j k N xi z v degree depth nextDegree nextDepth w E S
        (tail.take (N*CompanionBooleanPhase.stepBits A C K j k xi))
        (tail.drop (N*CompanionBooleanPhase.stepBits A C K j k xi)) := by
  dsimp only
  unfold input width
  change (((_,_),((_,N),tail.take (N*CompanionTransitionWidth.width
    (CompanionMetropolisWordProgram.packed
      (RootedLabelWeightProgram.config A C K j xi xi z v degree depth,matrixCode w)
      k (encodeSet (coordinateOrder A) S.val) [])))),
    tail.drop (N*CompanionTransitionWidth.width
      (CompanionMetropolisWordProgram.packed
        (RootedLabelWeightProgram.config A C K j xi xi z v degree depth,matrixCode w)
        k (encodeSet (coordinateOrder A) S.val) [])))=_
  rw [CompanionTransitionWidth.width_config]
  rfl


theorem run_sameLaw (padding : ℕ) (A : Instance (Fin m) (Fin n)) (C K j k N : ℕ)
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
    SameLaw (fun bits : Fin (N*CompanionBooleanPhase.stepBits A C K j k xi+
        ((N+1)*CompanionObservationQueriesProgram.blockWidth cs+padding))→Bool =>
      CompanionPhaseFinishProgram.view (p := (CanonicalInitialEncoding.copyOrder (capacities A)).length)
        (run cs (matrixCode w,E) k N (encodeSet (coordinateOrder A) S.val) (List.ofFn bits)))
      (fun bits : RootedPhaseTrial.TrialWords A C K j k N xi =>
        CompanionPhaseFinishProgram.storedView A (pairLabels A)
          ((RootedPhaseTrial.trial A (RootedCompletion.rowColumn A.T) C K j k N hK hW xi
            (RootedCatalogGrid.gridEquiv A K v) old S bits).getD old)) := by
  dsimp only
  let cs := CompanionObservationQueriesProgram.phaseConfigs A C K j xi z v degree depth nextDegree nextDepth
  let t := N*CompanionBooleanPhase.stepBits A C K j k xi
  let q := (N+1)*CompanionObservationQueriesProgram.blockWidth cs
  let project := CompanionPhaseFinishProgram.view (p := (CanonicalInitialEncoding.copyOrder (capacities A)).length)
  let oldView := CompanionPhaseFinishProgram.storedView A (pairLabels A) old
  have hold : project (matrixCode w,E)=oldView := by
    apply Prod.ext
    · funext i j
      exact (congrArg TreeFraction.val (readEntry_code w i j)).trans (hw i j)
    · exact hE
  have h := CompanionPhaseTrialProgram.trial_padded_sameLaw padding A C K j k N hC hj hK hW hB
    xi hxi z v degree depth nextDegree nextDepth hdegree hdepth hnextDegree hnextDepth old w E hw hE S
  dsimp only at h
  have hm := h.map (fun o => o.getD oldView)
  intro phi
  have he := uniformAverage_equiv (FairBits.splitWordEquiv t (q+padding))
    (fun p => phi (((CompanionPhaseTrialProgram.output (CompanionPhaseTrialProgram.data A C K j k N
      xi z v degree depth nextDegree nextDepth w E S (List.ofFn p.1) (List.ofFn p.2))).map project).getD oldView))
  have hleft (bits : Fin (t+(q+padding))→Bool) :
      project (run cs (matrixCode w,E) k N (encodeSet (coordinateOrder A) S.val) (List.ofFn bits))=
      (((CompanionPhaseTrialProgram.output (CompanionPhaseTrialProgram.data A C K j k N xi z v
        degree depth nextDegree nextDepth w E S
        (List.ofFn (FairBits.splitWordEquiv t (q+padding) bits).1)
        (List.ofFn (FairBits.splitWordEquiv t (q+padding) bits).2))).map project).getD oldView) := by
    unfold run
    rw [input_encoded]
    dsimp only [project] at hold ⊢
    rw [view_getD,hold,DensePrograms.ofFn_split_take,DensePrograms.ofFn_split_drop]
  have hright (bits : RootedPhaseTrial.TrialWords A C K j k N xi) :
      ((RootedPhaseTrial.trial A (RootedCompletion.rowColumn A.T) C K j k N hK hW xi
        (RootedCatalogGrid.gridEquiv A K v) old S bits).map
          (CompanionPhaseFinishProgram.storedView A (pairLabels A))).getD oldView=
      CompanionPhaseFinishProgram.storedView A (pairLabels A)
        ((RootedPhaseTrial.trial A (RootedCompletion.rowColumn A.T) C K j k N hK hW xi
          (RootedCatalogGrid.gridEquiv A K v) old S bits).getD old) := by
    cases RootedPhaseTrial.trial A (RootedCompletion.rowColumn A.T) C K j k N hK hW xi
      (RootedCatalogGrid.gridEquiv A K v) old S bits <;> rfl
  have hl : uniformAverage (fun bits : Fin (t+(q+padding))→Bool =>
      phi (project (run cs (matrixCode w,E) k N (encodeSet (coordinateOrder A) S.val) (List.ofFn bits))))=
      uniformAverage (fun p : (Fin t→Bool)×(Fin (q+padding)→Bool) => phi (((CompanionPhaseTrialProgram.output (CompanionPhaseTrialProgram.data A C K j k N
        xi z v degree depth nextDegree nextDepth w E S (List.ofFn p.1) (List.ofFn p.2))).map project).getD oldView)) := by
    simp_rw [hleft]
    exact he
  exact hl.trans ((hm phi).trans (by simp_rw [hright]))

end
end ContingencyTables.CompanionPhaseContinuation

end OAI
