import OAI.Combinatorics.ContingencyTables.Counting.CompanionTrajectoryProgram
import OAI.Combinatorics.ContingencyTables.Rooted.RootedReturnHistoryLaw
import OAI.Combinatorics.ContingencyTables.Rooted.RootedPhaseExperiment

namespace OAI

/-! # The executed observation trajectory has the selected-root source law -/
namespace ContingencyTables.CompanionTrajectoryProgram
open MatchingFPRAS CommonBasesFPRAS FirstSuccess ResidualMixture FiniteObservableTransport
open CompanionFactorialApplication CompanionComputedInitial CompanionComputedProposal
open CompanionArithmeticProposal CompanionOracleDensity CompanionWeightOracle
open CompanionEvaluatedWeightProgram CompanionMultiplierMatrixProgram CompanionPhaseTrajectory
open CompanionBooleanPhase (State)
open RealKernelApproximation GridBoundary
open scoped Classical
noncomputable section
variable {m n : ℕ}

theorem observations_sameLaw (A : Instance (Fin m) (Fin n)) (C K j k N : ℕ)
    (hC : 0 < C) (hj : j ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C)
    (xi : ℚ) (hxi : 0 < xi) (z : View A→ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (degree depth : List Bool)
    (hdegree : degree.length=PowerOfTwoApproximation.rootDegree (roundingTolerance (innerTolerance (xi/2) j)))
    (hdepth : depth.length=PowerOfTwoApproximation.depth (roundingTolerance (innerTolerance (xi/2) j)))
    (w : LabelIndex A→LabelIndex A→TreeFraction.Fraction) (S : State A) :
    SameLaw (fun bits : Fin (N*CompanionBooleanPhase.stepBits A C K j k xi)→Bool =>
      output (CompanionFlatReturnProgram.data A C K j k N xi z v degree depth w S (List.ofFn bits)))
      (fun bits : Fin (N*CompanionBooleanPhase.stepBits A C K j k xi)→Bool =>
        (List.ofFn (RootedPhaseExperiment.observedStates A (RootedCompletion.rowColumn A.T)
          C K j k N hK hW xi (RootedCatalogGrid.gridEquiv A K v) (sourceWeights A w) S bits)).map
            (encodeSet (coordinateOrder A))) := by
  let R := RootedCompletion.rowColumn A.T
  let v' := RootedCatalogGrid.gridEquiv A K v
  let sw := sourceWeights A w
  let F := RootedBooleanPhase.step A R C K j k hK hW xi v' sw
  let ret := fun a : PathState (State A) N =>
    (historyPrefix a).map (fun T => encodeSet (coordinateOrder A) T.val)
  have hb := RootedBooleanPhase.recordedWalk_law A R C K j k N N hK hW xi v' sw S
  have ha := RootedArithmeticStep.recordedWalk_law A R C K j k N N hK hW xi v' sw S
  have hm := (SameLaw.of_mapLaw_eq
    (RootedBooleanPhase.recordedWalk A R C K j k N N hK hW xi v' sw S)
    (RootedArithmeticStep.recordedWalk A R C K j k N N hK hW xi v' sw S)
    (hb.trans ha.symm)).map ret
  have hleft (bits : Fin (N*CompanionBooleanPhase.stepBits A C K j k xi)→Bool) :
      ret (RootedBooleanPhase.recordedWalk A R C K j k N N hK hW xi v' sw S bits)=
        (traceStates F S (List.ofFn (gridWordEquiv N (CompanionBooleanPhase.stepBits A C K j k xi) bits))).map
          (fun T => encodeSet (coordinateOrder A) T.val) := by
    unfold ret
    rw [show historyPrefix (RootedBooleanPhase.recordedWalk A R C K j k N N hK hW xi v' sw S bits)=
      traceStates F S (List.ofFn (gridWordEquiv N (CompanionBooleanPhase.stepBits A C K j k xi) bits)) from
      recorded_prefix F N S N le_rfl _]
  have hright (bits : Fin (N*CompanionBooleanPhase.stepBits A C K j k xi)→Bool) :
      ret (RootedArithmeticStep.recordedWalk A R C K j k N N hK hW xi v' sw S bits)=
        (List.ofFn (RootedPhaseExperiment.observedStates A R C K j k N hK hW xi v' sw S bits)).map
          (encodeSet (coordinateOrder A)) := by
    rw [RootedPhaseExperiment.observedStates_list]
    simp only [ret,List.map_map,Function.comp_def]
  intro phi
  have h := output_sameLaw A C K j k N hC hj hK hW hB xi hxi z v degree depth hdegree hdepth w S phi
  have hl : uniformAverage (fun bits => phi (ret
      (RootedBooleanPhase.recordedWalk A R C K j k N N hK hW xi v' sw S bits)))=
      uniformAverage (fun bits => phi ((traceStates F S
        (List.ofFn (gridWordEquiv N (CompanionBooleanPhase.stepBits A C K j k xi) bits))).map
          (fun T => encodeSet (coordinateOrder A) T.val))) := by
    apply congrArg uniformAverage
    funext bits
    exact congrArg phi (hleft bits)
  have hr : uniformAverage (fun bits => phi (ret
      (RootedArithmeticStep.recordedWalk A R C K j k N N hK hW xi v' sw S bits)))=
      uniformAverage (fun bits => phi ((List.ofFn (RootedPhaseExperiment.observedStates A R
        C K j k N hK hW xi v' sw S bits)).map (encodeSet (coordinateOrder A)))) := by
    apply congrArg uniformAverage
    funext bits
    exact congrArg phi (hright bits)
  exact h.trans (hl.symm.trans ((hm phi).trans hr))

end
end ContingencyTables.CompanionTrajectoryProgram

end OAI
