import OAI.Combinatorics.ContingencyTables.Counting.CompanionObservationPadding
import OAI.Combinatorics.ContingencyTables.Counting.CompanionCodeBounds

namespace OAI

/-! # The phase trial with an unused query suffix -/
namespace ContingencyTables.FiniteObservableTransport
open CommonBasesFPRAS FairBits
open scoped Classical
noncomputable section

theorem SameLaw.right_padding {U V Z : Type*} [Fintype U] [Fintype V] {n : ℕ}
    {f : U×(Fin n→Bool)→Z} {g : V→Z} (h : SameLaw f g) (padding : ℕ) :
    SameLaw (fun p : U×(Fin (n+padding)→Bool) => f (p.1,(splitWordEquiv n padding p.2).1)) g := by
  intro phi
  have hh := h phi
  rw [uniformAverage_prod] at hh ⊢
  refine Eq.trans ?_ hh
  apply congrArg uniformAverage
  funext u
  have he := uniformAverage_equiv (splitWordEquiv n padding)
    (fun p : (Fin n→Bool)×(Fin padding→Bool) => phi (f (u,p.1)))
  rw [uniformAverage_prod] at he
  simpa only [uniformAverage_const] using he

end
end ContingencyTables.FiniteObservableTransport

namespace ContingencyTables.CompanionPhaseTrialProgram
open MatchingFPRAS CompanionFactorialApplication CompanionComputedInitial CompanionComputedProposal
open CompanionArithmeticProposal CompanionEvaluatedWeightProgram CompanionMultiplierMatrixProgram
open CompanionOracleDensity CompanionWeightOracle GridBoundary FiniteObservableTransport CommonBasesFPRAS TwoLiftStates
open scoped Classical
noncomputable section
variable {m n : ℕ}

lemma trajectory_length_data (A : Instance (Fin m) (Fin n)) (C K j k N : ℕ) (xi : ℚ)
    (z : View A→ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (degree depth : List Bool) (w : LabelIndex A→LabelIndex A→TreeFraction.Fraction)
    (S : CompanionBooleanPhase.State A) (bits : Fin (N*CompanionBooleanPhase.stepBits A C K j k xi)→Bool) :
    (CompanionTrajectoryProgram.output
      (CompanionFlatReturnProgram.data A C K j k N xi z v degree depth w S (List.ofFn bits))).length=N+1 := by
  let state := CompanionFlatReturnProgram.stateData A C K j k xi z v degree depth w S
  let words := CompanionFlatReturnProgram.words
    (CompanionFlatReturnProgram.data A C K j k N xi z v degree depth w S (List.ofFn bits))
  have h := (CompanionCodeBounds.history_bound state words
    (TreeTyped.weight state.2+6*state.1.2.length+1) (by omega) (by omega)).2
  change (CompanionTrajectoryProgram.output
      (CompanionFlatReturnProgram.data A C K j k N xi z v degree depth w S (List.ofFn bits))).length=
      words.length+1 at h
  dsimp only [words] at h
  rw [CompanionFlatReturnProgram.words_data,List.length_ofFn] at h
  exact h

lemma output_data_take (A : Instance (Fin m) (Fin n)) (C K j k N : ℕ) (xi : ℚ)
    (z : View A→ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (degree depth nextDegree nextDepth : List Bool)
    (w : LabelIndex A→LabelIndex A→TreeFraction.Fraction) (E : TreeFraction.Fraction)
    (S : CompanionBooleanPhase.State A) (walkBits : Fin (N*CompanionBooleanPhase.stepBits A C K j k xi)→Bool)
    (queryBits : List Bool) :
    let cs := CompanionObservationQueriesProgram.phaseConfigs A C K j xi z v degree depth nextDegree nextDepth
    output (data A C K j k N xi z v degree depth nextDegree nextDepth w E S
      (List.ofFn walkBits) (queryBits.take ((N+1)*CompanionObservationQueriesProgram.blockWidth cs)))=
    output (data A C K j k N xi z v degree depth nextDegree nextDepth w E S
      (List.ofFn walkBits) queryBits) := by
  dsimp only
  have h := output_take
    ((data A C K j k N xi z v degree depth nextDegree nextDepth w E S (List.ofFn walkBits) queryBits).1)
    queryBits
  dsimp only [data] at h
  rw [trajectory_length_data] at h
  exact h


theorem trial_padded_sameLaw (padding : ℕ) (A : Instance (Fin m) (Fin n)) (C K j k N : ℕ)
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
        (Fin ((N+1)*CompanionObservationQueriesProgram.blockWidth cs+padding)→Bool) =>
      (output (data A C K j k N xi z v degree depth nextDegree nextDepth w E S
        (List.ofFn bits.1) (List.ofFn bits.2))).map (CompanionPhaseFinishProgram.view (p := (CanonicalInitialEncoding.copyOrder (capacities A)).length)))
      (fun bits : RootedPhaseTrial.TrialWords A C K j k N xi =>
        (RootedPhaseTrial.trial A (RootedCompletion.rowColumn A.T) C K j k N hK hW xi
          (RootedCatalogGrid.gridEquiv A K v) old S bits).map
            (CompanionPhaseFinishProgram.storedView A (pairLabels A))) := by
  dsimp only
  have h := trial_sameLaw A C K j k N hC hj hK hW hB xi hxi z v degree depth nextDegree nextDepth
    hdegree hdepth hnextDegree hnextDepth old w E hw hE S
  dsimp only at h
  have hp := h.right_padding padding
  intro phi
  have he (bits : (Fin (N*CompanionBooleanPhase.stepBits A C K j k xi)→Bool) ×
      (Fin ((N+1)*CompanionObservationQueriesProgram.blockWidth
        (CompanionObservationQueriesProgram.phaseConfigs A C K j xi z v degree depth nextDegree nextDepth)+padding)→Bool)) :
      output (data A C K j k N xi z v degree depth nextDegree nextDepth w E S
        (List.ofFn bits.1) (List.ofFn bits.2))=
      output (data A C K j k N xi z v degree depth nextDegree nextDepth w E S
        (List.ofFn bits.1) (List.ofFn (FairBits.splitWordEquiv _ padding bits.2).1)) := by
    rw [←output_data_take A C K j k N xi z v degree depth nextDegree nextDepth w E S bits.1
      (List.ofFn bits.2),DensePrograms.ofFn_split_take]
  simp_rw [he]
  exact hp phi

end
end ContingencyTables.CompanionPhaseTrialProgram

end OAI
