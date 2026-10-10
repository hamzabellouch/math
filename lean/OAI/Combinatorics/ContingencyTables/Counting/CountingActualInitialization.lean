import OAI.Combinatorics.ContingencyTables.Counting.CountingPositiveSemantics
import OAI.Combinatorics.ContingencyTables.Counting.CompanionStoredRepresentation

namespace OAI

/-! # Canonical physical initialization on the original bounded-table input -/
namespace ContingencyTables.CountingPositiveProgram
open MatchingFPRAS CompanionFactorialApplication CompanionComputedProposal GridBoundary
open scoped Classical
noncomputable section
variable {m n : ℕ}

theorem start_data (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0<epsilon)
    (delta : TreeFraction.Fraction) (bits : List Bool)
    (hlen : 2*Fintype.card (Labels (ComputedCountingParameters.data hEK r c b hne epsilon he)) ≤ bits.length) :
    let A := ComputedCountingParameters.data hEK r c b hne epsilon he
    let s := ComputedCountingParameters.settings hEK r c b hne epsilon he
    start (((NetworkVertexCode.data r c b,TreeFraction.repr epsilon),delta),bits)=
      (CompanionRestartInitializer.data A s.C s.K s.H
        (CompanionTargetMixing.restartTime A s.H s.L) s.N s.n s.L
        (CountingBaseProgram.half (TreeFraction.repr epsilon)) (fun _ => 0)
        (CountingPreparedState.start A s.K (ComputedCountingParameters.binCount_pos r c b epsilon he)),
       CompanionInitialStoredProgram.output (CompanionInitialStoredProgram.data A ∅)) := by
  let A := ComputedCountingParameters.data hEK r c b hne epsilon he
  let s := ComputedCountingParameters.settings hEK r c b hne epsilon he
  let x : CountingAdaptiveInputProgram.Input :=
    ((NetworkVertexCode.data r c b,TreeFraction.repr epsilon),bits)
  have hp := CountingAdaptiveInputProgram.prepared_data hEK r c b hne epsilon he bits
  have hc : CountingPreparedState.catalog x.1=RootedForestCatalog.data A :=
    CountingComputedSettings.catalog_data hEK r c b hne epsilon he
  have hw : CountingAdaptiveInputProgram.labelWidth x=2*Fintype.card (Labels A) := by
    unfold CountingAdaptiveInputProgram.labelWidth
    rw [CountingComputedSettings.labelCount_data hEK r c b hne epsilon he]
  apply Prod.ext hp
  change CountingAdaptiveInputProgram.initial x=_
  unfold CountingAdaptiveInputProgram.initial
  rw [CountingAdaptiveInputProgram.initialInput_data x A s.C s.K s.H
    (CompanionTargetMixing.restartTime A s.H s.L) s.N s.n s.L
    (CountingBaseProgram.half (TreeFraction.repr epsilon)) (fun _ => 0)
    (CountingPreparedState.start A s.K (ComputedCountingParameters.binCount_pos r c b epsilon he))
    hp hc hw hlen]

theorem start_rep (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0<epsilon)
    (delta : TreeFraction.Fraction) (bits : List Bool)
    (hlen : 2*Fintype.card (Labels (ComputedCountingParameters.data hEK r c b hne epsilon he)) ≤ bits.length) :
    let A := ComputedCountingParameters.data hEK r c b hne epsilon he
    CompanionStoredRepresentation.StoredRep
      (CanonicalInitialEncoding.copyOrder (CompanionComputedInitial.capacities A)).length
      (start (((NetworkVertexCode.data r c b,TreeFraction.repr epsilon),delta),bits)).2 := by
  rw [start_data hEK r c b hne epsilon he delta bits hlen]
  exact CompanionStoredRepresentation.initial_output_rep _ ∅

end
end ContingencyTables.CountingPositiveProgram

end OAI
