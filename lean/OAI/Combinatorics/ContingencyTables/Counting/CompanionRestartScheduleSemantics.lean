import OAI.Combinatorics.ContingencyTables.Counting.CompanionRestartSchedule
import OAI.Combinatorics.ContingencyTables.Counting.CompanionRestartDataLaw

namespace OAI

/-! # Exact deterministic restart budgets for the source experiment -/
namespace ContingencyTables.CompanionRestartSchedule
open MatchingFPRAS CompanionFactorialApplication CompanionOracleDensity
open CompanionComputedInitial GridBoundary FirstSuccess
open scoped BigOperators Classical
noncomputable section
variable {m n : ℕ}

lemma configInput_data (A : Instance (Fin m) (Fin n)) (C K H T N R L i : ℕ)
    (epsilon : TreeFraction.Fraction) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) :
    configInput (CompanionRestartInitializer.data A C K H T N R L epsilon z v,i)=
      RootedOracleConfigProgram.data A C K (i+1)
        (CountingPhaseParametersProgram.noise ([Fintype.card (Labels A),A.W,H,T,N,R,L],epsilon)) z v [] := rfl

lemma queryWidth_data (A : Instance (Fin m) (Fin n)) (C K H T N R L i : ℕ)
    (epsilon : TreeFraction.Fraction) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) :
    queryWidth (CompanionRestartInitializer.data A C K H T N R L epsilon z v,i)=
      CompanionOracleDensity.medianEstimatorBits A C K (i+1)
        (TreeFraction.val (CountingPhaseParametersProgram.noise ([Fintype.card (Labels A),A.W,H,T,N,R,L],epsilon)))
        (TreeFraction.val (CountingPhaseParametersProgram.noise ([Fintype.card (Labels A),A.W,H,T,N,R,L],epsilon))) := by
  rw [queryWidth,configInput_data,RootedOracleConfigProgram.wordWidth_data]

lemma proposalWidth_data (A : Instance (Fin m) (Fin n)) (C K H T N R L i : ℕ)
    (epsilon : TreeFraction.Fraction) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) :
    proposalWidth (CompanionRestartInitializer.data A C K H T N R L epsilon z v,i)=
      CompanionBooleanPhase.proposalBits A := by
  simp only [proposalWidth,scalar,CompanionRestartInitializer.data,
    CountingPhaseParametersProgram.scalar,ScalarScheduleProgram.Expr.eval,
    List.getD_cons_zero,CompanionBooleanPhase.proposalBits,pow_two]

theorem stageWidth_data (A : Instance (Fin m) (Fin n)) (C K H T N R L i : ℕ)
    (epsilon : TreeFraction.Fraction) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) :
    stageWidth (CompanionRestartInitializer.data A C K H T N R L epsilon z v,i)=
      CompanionRestartProgram.sourceWidth A C K
        ([Fintype.card (Labels A),A.W,H,T,N,R,L],epsilon) i := by
  unfold stageWidth
  change T*((R+1)*(1+(proposalWidth (CompanionRestartInitializer.data A C K H T N R L epsilon z v,i)+
    ((queryWidth (CompanionRestartInitializer.data A C K H T N R L epsilon z v,i)+
      queryWidth (CompanionRestartInitializer.data A C K H T N R L epsilon z v,i))+
        CountingPhaseParametersProgram.precision ([Fintype.card (Labels A),A.W,H,T,N,R,L],epsilon)))))=_
  rw [proposalWidth_data,queryWidth_data]
  rfl

theorem restartWidth_data (A : Instance (Fin m) (Fin n)) (C K H T N R L : ℕ)
    (epsilon : TreeFraction.Fraction) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (history : List CompanionPhaseFinishProgram.Stored) :
    restartWidth (CompanionRestartInitializer.data A C K H T N R L epsilon z v,history)=
      ∑ i : Fin history.length,CompanionRestartProgram.sourceWidth A C K
        ([Fintype.card (Labels A),A.W,H,T,N,R,L],epsilon) i.val := by
  unfold restartWidth indices
  rw [DirectedBFSCode.range_eq_map]
  simp only [List.map_map,Function.comp_def]
  rw [←List.ofFn_eq_map,List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro i _
  exact stageWidth_data A C K H T N R L i.val epsilon z v

lemma initialWidths_eq (A : Instance (Fin m) (Fin n)) (B : ℕ) :
    CompanionComputedInitial.wordLength A B=CompanionInitialDraw.initialBits A B := by
  unfold CompanionComputedInitial.wordLength CompanionInitialDraw.initialBits InitialFactorialBits.bitCount
  calc
    _ = ∑ s : SmallCell A,FixedCardinalityMixture.drawBits B (A.b s.val.1 s.val.2) :=
      Fintype.sum_equiv (CompanionComputedInitial.cellOrder A).symm _ _ (fun _ => rfl)
    _ = _ := (Fintype.sum_equiv (CompanionInitialDraw.cellEnum A).symm _ _ (fun _ => rfl)).symm

 /-- The physical width is exactly the initialized source-stage width,
 and depends on a history only through its length. -/
theorem width_data (A : Instance (Fin m) (Fin n)) (C K H N R L : ℕ)
    (epsilon : TreeFraction.Fraction) (z : View A → ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (history : List CompanionPhaseFinishProgram.Stored) :
    width (CompanionRestartInitializer.data A C K H (CompanionTargetMixing.restartTime A H L) N R L
      epsilon z v,history)=
      RootedRestartWords.initialStageBits A C K H L
        (CountingPhaseParametersProgram.precision
          ([Fintype.card (Labels A),A.W,H,CompanionTargetMixing.restartTime A H L,N,R,L],epsilon))
        R (CountingPhaseSchedule.initialPrecision H) history.length
        (TreeFraction.val (CountingPhaseParametersProgram.noise
          ([Fintype.card (Labels A),A.W,H,CompanionTargetMixing.restartTime A H L,N,R,L],epsilon))) := by
  rw [width,CompanionRestartInitializer.width_data,restartWidth_data,initialWidths_eq]
  rfl

end
end ContingencyTables.CompanionRestartSchedule

end OAI
