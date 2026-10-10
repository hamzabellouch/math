import OAI.Combinatorics.ContingencyTables.Counting.CountingActualPhase
import OAI.Combinatorics.ContingencyTables.Counting.CountingDirectSemantics
import OAI.Combinatorics.ContingencyTables.Counting.CompanionProjectedHistory
import OAI.Combinatorics.ContingencyTables.Counting.CountingPositiveWordLaw
import OAI.Combinatorics.ContingencyTables.Counting.ComputedCountingWords

namespace OAI

/-! # The actual original-input counting program has the source history law -/
namespace ContingencyTables.CountingPositiveProgram
open MatchingFPRAS CommonBasesFPRAS CompanionFactorialApplication GridBoundary FiniteObservableTransport
open scoped Classical
noncomputable section
variable {m n : ℕ}

attribute [local irreducible] CountingPositiveProgram.output CompanionOuterHistoryProgram.output
  CompanionOuterPhaseProgram.output

theorem value_source_sameLaw (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ) (he : 0<epsilon) :
    SameLaw
      (fun bits : Fin (bitCount (CountingDirectProgram.request r c b epsilon delta))→Bool =>
        TreeFraction.val (output (CountingDirectProgram.request r c b epsilon delta,List.ofFn bits)))
      (RootedCountingWords.flatEstimate (ComputedCountingParameters.data hEK r c b hne epsilon he)
        (ComputedCountingWords.root hEK r c b hne epsilon he)
        (ComputedCountingParameters.settings hEK r c b hne epsilon he)) := by
  let A := ComputedCountingParameters.data hEK r c b hne epsilon he
  let s := ComputedCountingParameters.settings hEK r c b hne epsilon he
  let req := CountingDirectProgram.request r c b epsilon delta
  let initial := CompanionInitialStoredProgram.output (CompanionInitialStoredProgram.data A ∅)
  let fixed := CountingActualPhase.fixed hEK r c b hne epsilon he initial
  let reserve := List.replicate (bitCount req) false
  have hlen : 2*Fintype.card (Labels A) ≤ reserve.length := by
    rw [List.length_replicate]
    exact initialReserve_le hEK r c b hne epsilon he (TreeFraction.repr delta)
  have hstart : start (req,reserve)=fixed :=
    start_data hEK r c b hne epsilon he (TreeFraction.repr delta) reserve hlen
  have hi := start_view hEK r c b hne epsilon he (TreeFraction.repr delta) reserve hlen
  change CompanionPhaseFinishProgram.view (start (req,reserve)).2 = _ at hi
  rw [hstart] at hi
  have hrep : CompanionStoredRepresentation.StoredRep
      (CanonicalInitialEncoding.copyOrder (CompanionComputedInitial.capacities A)).length initial :=
    CompanionStoredRepresentation.initial_output_rep A ∅
  have h := CompanionProjectedHistory.output_sameLaw A (CompanionComputedProposal.pairLabels A)
    (ComputedCountingWords.root hEK r c b hne epsilon he) s fixed hi
    (fun history hh hj => CountingActualPhase.output_rep hEK r c b hne epsilon he
      (TreeFraction.repr delta) initial hrep history hh hj)
    (fun history hh hj => CountingActualPhase.output_sameLaw hEK r c b hne epsilon he
      (TreeFraction.repr delta) initial hrep hi history hh hj)
  have hc : phaseCount req=s.H := phaseCount_data hEK r c b hne epsilon he (TreeFraction.repr delta)
  have hw := value_sameLaw req
  unfold independentOutput at hw
  rw [hstart,hc] at hw
  simp only [List.map_ofFn,Function.comp_def] at h
  intro phi
  have hf := uniformAverage_equiv (gridWordEquiv s.H (RootedPhaseHistory.totalWidth A s))
    (fun words => phi (RootedCountingWords.estimate A
      (ComputedCountingWords.root hEK r c b hne epsilon he) s words))
  exact (hw phi).trans ((h phi).trans hf.symm)

end
end ContingencyTables.CountingPositiveProgram

end OAI
