import OAI.Combinatorics.ContingencyTables.Counting.CompanionEvaluatedWeightProgram
import OAI.Combinatorics.ContingencyTables.Machines.FractionMetropolisProgram
import OAI.Combinatorics.ContingencyTables.Transport.FiniteObservableReindex

namespace OAI

/-! # Fixed-width laws for the two physical Metropolis weight calls -/

namespace ContingencyTables.CompanionEvaluatedWeightProgram

open MatchingFPRAS CompanionFactorialApplication CompanionComputedInitial
open CompanionArithmeticProposal CompanionOracleDensity CompanionWeightOracle
open CompanionMultiplierMatrixProgram GridBoundary CommonBasesFPRAS FiniteObservableTransport
open scoped Classical
noncomputable section
variable {m n : ℕ}

lemma queryWidth (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (xi : ℚ)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) :
    repetitionCount xi*RootedEstimatorLayoutProgram.wordWidth
      (RootedEstimatorMedianProgram.context A C K j xi z v)=medianEstimatorBits A C K j xi xi := by
  rw [RootedEstimatorMedianProgram.context,RootedEstimatorWordProgram.scheduledWordWidth]
  rfl

theorem sameLaw_fixed (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (hC : 0 < C) (hj : j ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=CompanionOracleDensity.binWidth A C)
    (xi : ℚ) (hxi : 0 < xi) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (degree depth : List Bool)
    (hdegree : degree.length=PowerOfTwoApproximation.rootDegree (roundingTolerance (innerTolerance (xi/2) j)))
    (hdepth : depth.length=PowerOfTwoApproximation.depth (roundingTolerance (innerTolerance (xi/2) j)))
    (w : LabelIndex A → LabelIndex A → TreeFraction.Fraction) (S : Set (Labels A × Bool)) :
    SameLaw (fun bits : WeightWord A C K j xi =>
      TreeFraction.val (output (((RootedLabelWeightProgram.config A C K j xi xi z v degree depth,matrixCode w),
        encodeSet (coordinateOrder A) S),List.ofFn bits)))
      (RootedOracleAcceptance.evaluatedWeight A (RootedCompletion.rowColumn A.T) C K j hK hW xi
        (RootedCatalogGrid.gridEquiv A K v) (sourceWeights A w) S) := by
  exact SameLaw.word_length (queryWidth A C K j xi (CompanionWeightOracle.profile A S) v)
    (fun bs => TreeFraction.val (output
      (((RootedLabelWeightProgram.config A C K j xi xi z v degree depth,matrixCode w),
        encodeSet (coordinateOrder A) S),bs))) _
    (sameLaw_evaluated A C K j hC hj hK hW hB xi hxi z v degree depth hdegree hdepth w S)

theorem acceptance_sameLaw (A : Instance (Fin m) (Fin n)) (C K j k : ℕ)
    (hC : 0 < C) (hj : j ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=CompanionOracleDensity.binWidth A C)
    (xi : ℚ) (hxi : 0 < xi) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (degree depth : List Bool)
    (hdegree : degree.length=PowerOfTwoApproximation.rootDegree (roundingTolerance (innerTolerance (xi/2) j)))
    (hdepth : depth.length=PowerOfTwoApproximation.depth (roundingTolerance (innerTolerance (xi/2) j)))
    (w : LabelIndex A → LabelIndex A → TreeFraction.Fraction) (S T : Set (Labels A × Bool)) :
    SameLaw (fun b : (WeightWord A C K j xi × WeightWord A C K j xi) × (Fin k → Bool) =>
      FractionMetropolisProgram.accept
        ((output (((RootedLabelWeightProgram.config A C K j xi xi z v degree depth,matrixCode w),
              encodeSet (coordinateOrder A) S),List.ofFn b.1.1),
          output (((RootedLabelWeightProgram.config A C K j xi xi z v degree depth,matrixCode w),
              encodeSet (coordinateOrder A) T),List.ofFn b.1.2)),List.ofFn b.2))
      (fun b : (WeightWord A C K j xi × WeightWord A C K j xi) × (Fin k → Bool) =>
        decide (FairBits.rationalThresholdAccept k
          (RootedOracleAcceptance.acceptance A (RootedCompletion.rowColumn A.T) C K j hK hW xi
            (RootedCatalogGrid.gridEquiv A K v) (sourceWeights A w) S T b.1) b.2)) := by
  exact FractionMetropolisProgram.sameLaw_accept _ _ _ _
    (sameLaw_fixed A C K j hC hj hK hW hB xi hxi z v degree depth hdegree hdepth w S)
    (sameLaw_fixed A C K j hC hj hK hW hB xi hxi z v degree depth hdegree hdepth w T) k

end
end ContingencyTables.CompanionEvaluatedWeightProgram

end OAI
