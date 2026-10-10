import OAI.Combinatorics.ContingencyTables.Counting.CountingActualSettings
import OAI.Combinatorics.ContingencyTables.Counting.CompanionCanonicalPhaseSupport

namespace OAI

/-! # Executed phases with the controls computed from the original input -/
namespace ContingencyTables.CountingActualPhase
open MatchingFPRAS CommonBasesFPRAS FiniteObservableTransport
open CompanionFactorialApplication CompanionComputedInitial CompanionComputedProposal
open CompanionStoredRepresentation CompanionCanonicalHistory CompanionOracleDensity GridBoundary
open scoped Classical
noncomputable section
variable {m n : ℕ}

def fixed (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0 < epsilon)
    (initial : CompanionPhaseFinishProgram.Stored) : CompanionOuterHistoryProgram.Fixed :=
  let A := ComputedCountingParameters.data hEK r c b hne epsilon he
  let s := ComputedCountingParameters.settings hEK r c b hne epsilon he
  (CompanionRestartInitializer.data A s.C s.K s.H
    (CompanionTargetMixing.restartTime A s.H s.L) s.N s.n s.L
    (CountingBaseProgram.half (TreeFraction.repr epsilon)) (fun _ => 0)
    (CountingPreparedState.start A s.K (ComputedCountingParameters.binCount_pos r c b epsilon he)),initial)

lemma phase_bounds (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0 < epsilon)
    (delta : TreeFraction.Fraction) (j : ℕ)
    (hj : j < (ComputedCountingParameters.settings hEK r c b hne epsilon he).H) :
    let A := ComputedCountingParameters.data hEK r c b hne epsilon he
    let s := ComputedCountingParameters.settings hEK r c b hne epsilon he
    let W := CountingPositiveProgram.phaseWidth ((NetworkVertexCode.data r c b,TreeFraction.repr epsilon),delta)
    RootedPhaseHistory.totalWidth A s ≤ W ∧ j+1 ≤ rationalHeight A s.C ∧
      (∀ i,i ≤ j+1 → PowerOfTwoApproximation.rootDegree
        (roundingTolerance (innerTolerance (s.xi/2) i)) ≤ W) ∧
      (∀ i,i ≤ j+1 → PowerOfTwoApproximation.depth
        (roundingTolerance (innerTolerance (s.xi/2) i)) ≤ W) := by
  dsimp only
  have hc := CountingPositiveProgram.phaseWidth_covers hEK r c b hne epsilon he delta
  have hj' : j+1 ≤ (ComputedCountingParameters.settings hEK r c b hne epsilon he).H :=
    Nat.succ_le_of_lt hj
  refine ⟨hc.1,hj'.trans (CountingActualSettings.height hEK r c b hne epsilon he),?_,?_⟩
  · intro i hi
    have hm := hc.2.1 i (hi.trans hj')
    omega
  · intro i hi
    have hm := hc.2.1 i (hi.trans hj')
    omega

theorem output_rep (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0 < epsilon)
    (delta : TreeFraction.Fraction) (initial : CompanionPhaseFinishProgram.Stored)
    (hinit : StoredRep (CanonicalInitialEncoding.copyOrder
      (capacities (ComputedCountingParameters.data hEK r c b hne epsilon he))).length initial)
    (history : List CompanionPhaseFinishProgram.Stored)
    (hh : ∀ q∈history,StoredRep (CanonicalInitialEncoding.copyOrder
      (capacities (ComputedCountingParameters.data hEK r c b hne epsilon he))).length q)
    (hj : history.length < (ComputedCountingParameters.settings hEK r c b hne epsilon he).H)
    (bits : Fin (CountingPositiveProgram.phaseWidth
      ((NetworkVertexCode.data r c b,TreeFraction.repr epsilon),delta))→Bool) :
    StoredRep (CanonicalInitialEncoding.copyOrder
      (capacities (ComputedCountingParameters.data hEK r c b hne epsilon he))).length
      (CompanionOuterPhaseProgram.output
        ((fixed hEK r c b hne epsilon he initial,history),List.ofFn bits)) := by
  let A := ComputedCountingParameters.data hEK r c b hne epsilon he
  let s := ComputedCountingParameters.settings hEK r c b hne epsilon he
  let e := CountingBaseProgram.half (TreeFraction.repr epsilon)
  let v := CountingPreparedState.start A s.K (ComputedCountingParameters.binCount_pos r c b epsilon he)
  let W := CountingPositiveProgram.phaseWidth ((NetworkVertexCode.data r c b,TreeFraction.repr epsilon),delta)
  have hr : CompanionCanonicalPhaseLaw.rawSettings A s.C s.K s.H s.N s.n s.L e s.hK s.hW v=s :=
    CountingActualSettings.raw_settings hEK r c b hne epsilon he
  have hb := phase_bounds hEK r c b hne epsilon he delta history.length hj
  have hwidth : RootedPhaseHistory.totalWidth A
      (CompanionCanonicalPhaseLaw.rawSettings A s.C s.K s.H s.N s.n s.L e s.hK s.hW v) ≤ W := by
    rw [hr]
    exact hb.1
  have hd : ∀ i,i ≤ history.length+1 → PowerOfTwoApproximation.rootDegree
      (roundingTolerance (innerTolerance
        ((CompanionCanonicalPhaseLaw.rawSettings A s.C s.K s.H s.N s.n s.L e s.hK s.hW v).xi/2) i)) ≤ W := by
    rw [hr]
    exact hb.2.2.1
  have ht : ∀ i,i ≤ history.length+1 → PowerOfTwoApproximation.depth
      (roundingTolerance (innerTolerance
        ((CompanionCanonicalPhaseLaw.rawSettings A s.C s.K s.H s.N s.n s.L e s.hK s.hW v).xi/2) i)) ≤ W := by
    rw [hr]
    exact hb.2.2.2
  exact CompanionCanonicalPhaseSupport.output_rep A s.C s.K s.H s.N s.n s.L W e
    (CountingActualSettings.coefficient_pos hEK r c b hne epsilon he) s.hK s.hW
    (CountingActualSettings.bin_width hEK r c b hne epsilon he)
    (CountingActualSettings.noise_pos hEK r c b hne epsilon he)
    (fun _ => 0) v initial history hj hb.2.1 hwidth hd ht hinit hh bits

theorem output_sameLaw (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0 < epsilon)
    (delta : TreeFraction.Fraction) (initial : CompanionPhaseFinishProgram.Stored)
    (hinit : StoredRep (CanonicalInitialEncoding.copyOrder
      (capacities (ComputedCountingParameters.data hEK r c b hne epsilon he))).length initial)
    (hi : CompanionPhaseFinishProgram.view
      (p := (CanonicalInitialEncoding.copyOrder
        (capacities (ComputedCountingParameters.data hEK r c b hne epsilon he))).length) initial=
      project (ComputedCountingParameters.data hEK r c b hne epsilon he)
        (pairLabels (ComputedCountingParameters.data hEK r c b hne epsilon he))
        (RootedStoredEstimate.initialStored (ComputedCountingParameters.data hEK r c b hne epsilon he)))
    (history : List CompanionPhaseFinishProgram.Stored)
    (hh : ∀ q∈history,StoredRep (CanonicalInitialEncoding.copyOrder
      (capacities (ComputedCountingParameters.data hEK r c b hne epsilon he))).length q)
    (hj : history.length < (ComputedCountingParameters.settings hEK r c b hne epsilon he).H) :
    let A := ComputedCountingParameters.data hEK r c b hne epsilon he
    let s := ComputedCountingParameters.settings hEK r c b hne epsilon he
    SameLaw (fun bits : Fin (CountingPositiveProgram.phaseWidth
      ((NetworkVertexCode.data r c b,TreeFraction.repr epsilon),delta))→Bool =>
      CompanionPhaseFinishProgram.view (p := (CanonicalInitialEncoding.copyOrder (capacities A)).length)
        (CompanionOuterPhaseProgram.output
          ((fixed hEK r c b hne epsilon he initial,history),List.ofFn bits)))
      (fun bits : RootedPhaseHistory.Word A s => canonicalStep A (pairLabels A)
        (RootedCompletion.rowColumn A.T) s
        (history.map (CompanionPhaseFinishProgram.view
          (p := (CanonicalInitialEncoding.copyOrder (capacities A)).length))) bits) := by
  dsimp only
  let A := ComputedCountingParameters.data hEK r c b hne epsilon he
  let s := ComputedCountingParameters.settings hEK r c b hne epsilon he
  let e := CountingBaseProgram.half (TreeFraction.repr epsilon)
  let v := CountingPreparedState.start A s.K (ComputedCountingParameters.binCount_pos r c b epsilon he)
  let W := CountingPositiveProgram.phaseWidth ((NetworkVertexCode.data r c b,TreeFraction.repr epsilon),delta)
  have hr : CompanionCanonicalPhaseLaw.rawSettings A s.C s.K s.H s.N s.n s.L e s.hK s.hW v=s :=
    CountingActualSettings.raw_settings hEK r c b hne epsilon he
  have hb := phase_bounds hEK r c b hne epsilon he delta history.length hj
  have hwidth : RootedPhaseHistory.totalWidth A
      (CompanionCanonicalPhaseLaw.rawSettings A s.C s.K s.H s.N s.n s.L e s.hK s.hW v) ≤ W := by
    rw [hr]
    exact hb.1
  have hd : ∀ i,i ≤ history.length+1 → PowerOfTwoApproximation.rootDegree
      (roundingTolerance (innerTolerance
        ((CompanionCanonicalPhaseLaw.rawSettings A s.C s.K s.H s.N s.n s.L e s.hK s.hW v).xi/2) i)) ≤ W := by
    rw [hr]
    exact hb.2.2.1
  have ht : ∀ i,i ≤ history.length+1 → PowerOfTwoApproximation.depth
      (roundingTolerance (innerTolerance
        ((CompanionCanonicalPhaseLaw.rawSettings A s.C s.K s.H s.N s.n s.L e s.hK s.hW v).xi/2) i)) ≤ W := by
    rw [hr]
    exact hb.2.2.2
  have h := CompanionCanonicalPhaseLaw.output_sameLaw A s.C s.K s.H s.N s.n s.L W e
    (CountingActualSettings.coefficient_pos hEK r c b hne epsilon he) s.hK s.hW
    (CountingActualSettings.bin_width hEK r c b hne epsilon he)
    (CountingActualSettings.noise_pos hEK r c b hne epsilon he)
    (fun _ => 0) v initial history hj hb.2.1 hwidth hd ht hinit hh hi
  dsimp only at h
  rw [hr] at h
  exact h

end
end ContingencyTables.CountingActualPhase

end OAI
