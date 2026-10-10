import OAI.Combinatorics.ContingencyTables.Counting.CompanionPhaseContinuation

namespace OAI

/-! # Binding a restart law to its independent phase continuation -/
namespace ContingencyTables.FiniteObservableTransport
open CommonBasesFPRAS
noncomputable section

theorem joint_encoded_bind {A B U V C Z W : Type*}
    [Fintype A] [Fintype B] [Fintype U] [Fintype V]
    (f : A → C×U) (g : B → Z) (e : Z → C)
    (F : C → U → W) (G : Z → V → W)
    (hinit : SameLaw f (fun p : B×U => (e (g p.1),p.2)))
    (hstep : ∀ z,SameLaw (F (e z)) (G z)) :
    SameLaw (fun a => F (f a).1 (f a).2) (fun p : B×V => G (g p.1) p.2) := by
  intro phi
  have hi := hinit (fun p => phi (F p.1 p.2))
  refine hi.trans ?_
  rw [uniformAverage_prod,uniformAverage_prod]
  apply congrArg uniformAverage
  funext b
  exact hstep (g b) phi

end
end ContingencyTables.FiniteObservableTransport

namespace ContingencyTables.CompanionOuterPhaseProgram
open MatchingFPRAS CommonBasesFPRAS CompanionFactorialApplication CompanionComputedInitial
open CompanionComputedProposal CompanionArithmeticProposal CompanionEvaluatedWeightProgram
open CompanionMultiplierMatrixProgram CompanionOracleDensity GridBoundary FiniteObservableTransport
open scoped Classical
noncomputable section
variable {m n : ℕ}

def configs (A : Instance (Fin m) (Fin n)) (C K H T N R L j : ℕ)
    (epsilon : TreeFraction.Fraction) (z : View A→ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool) :
    CompanionPhaseContinuation.Configs :=
  let p := CompanionInitializedRestartProgram.parameters A H T N R L epsilon
  CompanionObservationQueriesProgram.phaseConfigs A C K j
    (TreeFraction.val (CountingPhaseParametersProgram.noise p)) z v
    (CompanionRestartStageProgram.degree A C K j p z v reserve)
    (CompanionRestartStageProgram.depth A C K j p z v reserve)
    (CompanionRestartStageProgram.degree A C K (j+1) p z v reserve)
    (CompanionRestartStageProgram.depth A C K (j+1) p z v reserve)

lemma output_data_run (A : Instance (Fin m) (Fin n)) (C K H T N R L j : ℕ)
    (epsilon : TreeFraction.Fraction) (z : View A→ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (w : ℕ→LabelIndex A→LabelIndex A→TreeFraction.Fraction)
    (E : ℕ→TreeFraction.Fraction) (reserve bits : List Bool)
    (hlen : bits.length=reserve.length) :
    output (data A C K H T N R L j epsilon z v w E bits)=
      CompanionPhaseContinuation.run (configs A C K H T N R L j epsilon z v reserve)
        (matrixCode (w j),E j)
        (CountingPhaseParametersProgram.precision
          (CompanionInitializedRestartProgram.parameters A H T N R L epsilon))
        (CountingPhaseParametersProgram.observations
          (CompanionInitializedRestartProgram.parameters A H T N R L epsilon))
        (CompanionInitializedRestartProgram.output
          (CompanionInitializedRestartProgram.data A C K H T N R L j epsilon z v w
            (fun i => E (i.val+1)) bits))
        (bits.drop (wordLength A
          (CompanionInitialDraw.precision A (CountingPhaseSchedule.initialPrecision H))+
          CompanionRestartProgram.sumBits A C K j
            (CompanionInitializedRestartProgram.parameters A H T N R L epsilon))) := by
  rw [CompanionPhaseContinuation.outer_eq,configAt_data,configAt_data,old_data]
  unfold startCode afterRestart
  rw [restartInput_data,restartWidth_data]
  simp only [Nat.add_zero]
  unfold configs CompanionObservationQueriesProgram.phaseConfigs
  simp only [CompanionRestartStageProgram.degree,CompanionRestartStageProgram.depth,
    CompanionRestartStageProgram.oracleData,hlen]
  rfl

end
end ContingencyTables.CompanionOuterPhaseProgram

end OAI
