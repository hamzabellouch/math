import OAI.Combinatorics.ContingencyTables.Counting.CountingAdaptiveInputProgram
import OAI.Combinatorics.ContingencyTables.Counting.CompanionPhaseFinishSemantics

namespace OAI

/-! # The computed initial record is the literal adaptive counting record -/
namespace ContingencyTables.CountingAdaptiveInputProgram
open MatchingFPRAS CompanionFactorialApplication CompanionComputedInitial CompanionComputedProposal
open CompanionArithmeticProposal CompanionMultiplierMatrixProgram TwoLiftStates GridBoundary
open scoped Classical
noncomputable section
variable {m n : ℕ}

theorem prepared_data (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0 < epsilon)
    (reserve : List Bool) :
    let A := ComputedCountingParameters.data hEK r c b hne epsilon he
    let s := ComputedCountingParameters.settings hEK r c b hne epsilon he
    prepared ((NetworkVertexCode.data r c b,TreeFraction.repr epsilon),reserve)=
      CompanionRestartInitializer.data A s.C s.K s.H
        (CompanionTargetMixing.restartTime A s.H s.L) s.N s.n s.L
        (CountingBaseProgram.half (TreeFraction.repr epsilon)) (fun _ => 0)
        (CountingPreparedState.start A s.K (ComputedCountingParameters.binCount_pos r c b epsilon he)) := by
  dsimp only
  unfold prepared CountingPreparedState.output
  rw [CountingPreparedState.state_data hEK r c b hne epsilon he,
    CountingComputedSettings.parameters_data hEK r c b hne epsilon he]
  rfl

lemma zeroCode_data (x : Input) (A : Instance (Fin m) (Fin n))
    (hw : labelWidth x=2*Fintype.card (Labels A))
    (hr : 2*Fintype.card (Labels A) ≤ x.2.length) :
    zeroCode x=encodeSet (coordinateOrder A) ∅ := by
  have hcard : (CanonicalInitialEncoding.pairOrder (CompanionComputedInitial.capacities A)).length=
      2*Fintype.card (Labels A) := by
    have h := (Fintype.card_congr (coordinateOrder A)).symm
    simpa only [Fintype.card_fin,Fintype.card_prod,Fintype.card_bool,Nat.mul_comm] using h
  have he : ProfilePrograms.setProfile (coordinateSet (coordinateOrder A) ∅)=
      (fun _ => (0:ℕ)) := by
    funext i
    simp only [ProfilePrograms.setProfile,coordinateSet,Set.mem_preimage,Set.mem_empty_iff_false,ite_false]
  rw [zeroCode,List.map_const',List.length_take,hw,min_eq_left hr,encodeSet,he,List.ofFn_const,hcard]

lemma initialInput_data (x : Input) (A : Instance (Fin m) (Fin n))
    (C K H T N R L : ℕ) (epsilon : TreeFraction.Fraction)
    (z : View A→ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (hp : prepared x=CompanionRestartInitializer.data A C K H T N R L epsilon z v)
    (hc : CountingPreparedState.catalog x.1=RootedForestCatalog.data A)
    (hw : labelWidth x=2*Fintype.card (Labels A))
    (hr : 2*Fintype.card (Labels A) ≤ x.2.length) :
    initialInput x=CompanionInitialStoredProgram.data A ∅ := by
  have hb : capacities x=List.ofFn (CompanionComputedInitial.capacities A) := by
    unfold capacities CompanionRestartInitializer.capacities
    rw [hp,CompanionRestartInitializer.cellInput_data,CompanionCellCatalog.capacities_eq]
    rfl
  unfold initialInput CompanionInitialStoredProgram.data
  rw [hc,hb,zeroCode_data x A hw hr]

theorem initial_view (x : Input) (A : Instance (Fin m) (Fin n))
    (C K H T N R L : ℕ) (epsilon : TreeFraction.Fraction)
    (z : View A→ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (hp : prepared x=CompanionRestartInitializer.data A C K H T N R L epsilon z v)
    (hc : CountingPreparedState.catalog x.1=RootedForestCatalog.data A)
    (hw : labelWidth x=2*Fintype.card (Labels A))
    (hr : 2*Fintype.card (Labels A) ≤ x.2.length) :
    CompanionPhaseFinishProgram.view (initial x)=
      CompanionPhaseFinishProgram.storedView A (pairLabels A) (RootedStoredEstimate.initialStored A) := by
  rw [initial,initialInput_data x A C K H T N R L epsilon z v hp hc hw hr]
  apply Prod.ext
  · funext i j
    change TreeFraction.val (readEntry ((CompanionInitialStoredProgram.output
      (CompanionInitialStoredProgram.data A ∅)).1,(i.val,j.val)))=_
    rw [CompanionInitialStoredProgram.output_matrix,readEntry_code]
    exact CompanionInitialMatrixProgram.initialEntries_val A i j
  · exact CompanionInitialStoredProgram.total_data A ∅

end
end ContingencyTables.CountingAdaptiveInputProgram

end OAI
