import OAI.Combinatorics.ContingencyTables.Counting.CompanionFlatReturnProgram

namespace OAI

/-! # The flat executed observation trajectory, including its initial state -/
namespace ContingencyTables.CompanionTrajectoryProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped
abbrev Input := CompanionFlatReturnProgram.Input

def output (z : Input) : List (List ℕ) :=
  CompanionBoundedWalkProgram.history (CompanionFlatReturnProgram.returnInput z)
def outputRealizer : Realizer output :=
  composition (f := CompanionFlatReturnProgram.returnInput) (g := CompanionBoundedWalkProgram.history)
    CompanionFlatReturnProgram.returnInputRealizer CompanionBoundedWalkProgram.historyRealizer
lemma polynomial_output : PolynomialTime outputRealizer :=
  polynomial_composition CompanionFlatReturnProgram.polynomial_returnInput
    CompanionBoundedWalkProgram.polynomial_history

open CommonBasesFPRAS CompanionFactorialApplication CompanionComputedInitial CompanionComputedProposal
open CompanionArithmeticProposal CompanionOracleDensity CompanionWeightOracle
open CompanionEvaluatedWeightProgram CompanionMultiplierMatrixProgram FiniteObservableTransport
open TwoLiftStates GridBoundary
open scoped Classical
noncomputable section
variable {m n : ℕ}

theorem output_sameLaw (A : Instance (Fin m) (Fin n)) (C K j k N : ℕ)
    (hC : 0 < C) (hj : j ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C)
    (xi : ℚ) (hxi : 0 < xi) (z : View A→ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (degree depth : List Bool)
    (hdegree : degree.length=PowerOfTwoApproximation.rootDegree (roundingTolerance (innerTolerance (xi/2) j)))
    (hdepth : depth.length=PowerOfTwoApproximation.depth (roundingTolerance (innerTolerance (xi/2) j)))
    (w : LabelIndex A→LabelIndex A→TreeFraction.Fraction) (S : CompanionBooleanPhase.State A) :
    SameLaw (fun bits : Fin (N*CompanionBooleanPhase.stepBits A C K j k xi)→Bool =>
      output (CompanionFlatReturnProgram.data A C K j k N xi z v degree depth w S (List.ofFn bits)))
      (fun bits : Fin (N*CompanionBooleanPhase.stepBits A C K j k xi)→Bool =>
        (traceStates (RootedBooleanPhase.step A (RootedCompletion.rowColumn A.T) C K j k hK hW xi
          (RootedCatalogGrid.gridEquiv A K v) (sourceWeights A w)) S
            (List.ofFn (gridWordEquiv N (CompanionBooleanPhase.stepBits A C K j k xi) bits))).map
              (fun T => encodeSet (coordinateOrder A) T.val)) := by
  let state := CompanionFlatReturnProgram.stateData A C K j k xi z v degree depth w S
  have hs := CompanionBoundedWalkProgram.history_sameLaw A C K j k hC hj hK hW hB xi hxi
    z v degree depth hdegree hdepth w S N
  dsimp only at hs
  intro phi
  have hl := uniformAverage_equiv (gridWordEquiv N (CompanionBooleanPhase.stepBits A C K j k xi))
    (fun ws => phi (CompanionBoundedWalkProgram.history
      (state,List.ofFn (fun i => List.ofFn (ws i)))))
  have hr := uniformAverage_equiv (gridWordEquiv N (CompanionBooleanPhase.stepBits A C K j k xi))
    (fun ws => phi ((traceStates (RootedBooleanPhase.step A (RootedCompletion.rowColumn A.T)
      C K j k hK hW xi (RootedCatalogGrid.gridEquiv A K v) (sourceWeights A w)) S
        (List.ofFn ws)).map (fun T => encodeSet (coordinateOrder A) T.val)))
  have ho (bits : Fin (N*CompanionBooleanPhase.stepBits A C K j k xi)→Bool) :
      output (CompanionFlatReturnProgram.data A C K j k N xi z v degree depth w S (List.ofFn bits))=
        CompanionBoundedWalkProgram.history (state,List.ofFn (fun i => List.ofFn
          (gridWordEquiv N (CompanionBooleanPhase.stepBits A C K j k xi) bits i))) := by
    change CompanionBoundedWalkProgram.history
      (state,CompanionFlatReturnProgram.words
        (CompanionFlatReturnProgram.data A C K j k N xi z v degree depth w S (List.ofFn bits)))=_
    rw [CompanionFlatReturnProgram.words_data]
  have he : uniformAverage (fun bits : Fin (N*CompanionBooleanPhase.stepBits A C K j k xi)→Bool =>
      phi (output (CompanionFlatReturnProgram.data A C K j k N xi z v degree depth w S (List.ofFn bits))))=
      uniformAverage (fun bits => phi (CompanionBoundedWalkProgram.history
        (state,List.ofFn (fun i => List.ofFn (gridWordEquiv N (CompanionBooleanPhase.stepBits A C K j k xi) bits i))))) := by
    apply congrArg uniformAverage
    funext bits
    exact congrArg phi (ho bits)
  exact he.trans (hl.trans ((hs phi).trans hr.symm))

end
end ContingencyTables.CompanionTrajectoryProgram

end OAI
