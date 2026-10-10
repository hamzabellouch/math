import OAI.Combinatorics.ContingencyTables.Counting.CountingPositiveProgram
import OAI.Combinatorics.ContingencyTables.Counting.CountingAdaptiveInputSemantics
import OAI.Combinatorics.ContingencyTables.Counting.CompanionUniformPhaseBounds
import OAI.Combinatorics.ContingencyTables.Counting.CountingAdaptiveReserve

namespace OAI

/-! # Original-input semantics of the positive counting adapter -/
namespace ContingencyTables.CountingPositiveProgram
open MatchingFPRAS CompanionFactorialApplication CompanionComputedProposal GridBoundary
open scoped Classical
noncomputable section
variable {m n : ℕ}

theorem prepared_data (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0 < epsilon)
    (delta : TreeFraction.Fraction) :
    let A := ComputedCountingParameters.data hEK r c b hne epsilon he
    let s := ComputedCountingParameters.settings hEK r c b hne epsilon he
    prepared ((NetworkVertexCode.data r c b,TreeFraction.repr epsilon),delta)=
      CompanionUniformPhaseWidth.data A s
        (CountingBaseProgram.half (TreeFraction.repr epsilon)) (fun _ => 0)
        (CountingPreparedState.start A s.K (ComputedCountingParameters.binCount_pos r c b epsilon he)) := by
  exact CountingAdaptiveInputProgram.prepared_data hEK r c b hne epsilon he []

theorem phaseCount_data (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0 < epsilon)
    (delta : TreeFraction.Fraction) :
    phaseCount ((NetworkVertexCode.data r c b,TreeFraction.repr epsilon),delta)=
      (ComputedCountingParameters.settings hEK r c b hne epsilon he).H := by
  unfold phaseCount
  rw [prepared_data hEK r c b hne epsilon he delta]
  rfl

theorem start_prepared (z : Input) : (start z).1=prepared z.1 := rfl

theorem start_ofFn (req : Request) (N : ℕ) (bits : Fin N→Bool) :
    start (req,List.ofFn bits)=start (req,List.replicate N false) :=
  CountingAdaptiveInputProgram.output_ofFn req.1 N bits

theorem start_view (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0 < epsilon)
    (delta : TreeFraction.Fraction) (bits : List Bool)
    (hlen : 2*Fintype.card (Labels (ComputedCountingParameters.data hEK r c b hne epsilon he)) ≤ bits.length) :
    let A := ComputedCountingParameters.data hEK r c b hne epsilon he
    CompanionPhaseFinishProgram.view
      ((start (((NetworkVertexCode.data r c b,TreeFraction.repr epsilon),delta),bits)).2)=
      CompanionPhaseFinishProgram.storedView A (pairLabels A) (RootedStoredEstimate.initialStored A) := by
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
  exact CountingAdaptiveInputProgram.initial_view x A s.C s.K s.H
    (CompanionTargetMixing.restartTime A s.H s.L) s.N s.n s.L
    (CountingBaseProgram.half (TreeFraction.repr epsilon)) (fun _ => 0)
    (CountingPreparedState.start A s.K (ComputedCountingParameters.binCount_pos r c b epsilon he))
    hp hc hw hlen

theorem output_ofFn (req : Request) (bits : Fin (bitCount req)→Bool) :
    output (req,List.ofFn bits)=
      (CompanionOuterHistoryProgram.output
        (start (req,List.ofFn bits),List.ofFn (fun i : Fin (phaseCount req) =>
          List.ofFn (fun j : Fin (phaseWidth req) => bits (finProdFinEquiv (i,j)))))).2 := by
  unfold output finalStored historyInput
  rw [words_ofFn]

theorem phases_pos (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0 < epsilon) :
    0 < (ComputedCountingParameters.settings hEK r c b hne epsilon he).H := by
  have hC := ComputedCountingParameters.coefficient_pos r c b epsilon he
  have hd : 0 < ComputedCountingParameters.dimensionAllowance (m := m) (n := n) := by
    unfold ComputedCountingParameters.dimensionAllowance
    omega
  change 0 < ComputedCountingParameters.phases r c b epsilon
  unfold ComputedCountingParameters.phases
  positivity

theorem phaseWidth_covers (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0 < epsilon)
    (delta : TreeFraction.Fraction) :
    let A := ComputedCountingParameters.data hEK r c b hne epsilon he
    let s := ComputedCountingParameters.settings hEK r c b hne epsilon he
    let W := phaseWidth ((NetworkVertexCode.data r c b,TreeFraction.repr epsilon),delta)
    RootedPhaseHistory.totalWidth A s ≤ W ∧
      (∀ j,j ≤ s.H →
        PowerOfTwoApproximation.rootDegree
            (CompanionOracleDensity.roundingTolerance (CompanionOracleDensity.innerTolerance (s.xi/2) j))+
          PowerOfTwoApproximation.depth
            (CompanionOracleDensity.roundingTolerance (CompanionOracleDensity.innerTolerance (s.xi/2) j)) ≤ W) ∧
      2*Fintype.card (Labels A) ≤ W := by
  let A := ComputedCountingParameters.data hEK r c b hne epsilon he
  let s := ComputedCountingParameters.settings hEK r c b hne epsilon he
  let e := CountingBaseProgram.half (TreeFraction.repr epsilon)
  let v := CountingPreparedState.start A s.K
    (ComputedCountingParameters.binCount_pos r c b epsilon he)
  have hk := CountingComputedSettings.precision_data hEK r c b hne epsilon he
  rw [CountingComputedSettings.parameters_data hEK r c b hne epsilon he] at hk
  have hp : 0 < s.k := CountingPhaseSchedule.precision_pos _ _ _ _ _
  have hc := CompanionUniformPhaseWidth.width_covers A s e (fun _ => 0) v hk
    (show s.h=CountingPhaseSchedule.initialPrecision s.H from rfl)
    (show s.xi=1/(s.k:ℚ) from rfl) hp
    (phases_pos hEK r c b hne epsilon he) (le_refl _)
  have hw := congrArg CompanionUniformPhaseWidth.width
    (prepared_data hEK r c b hne epsilon he delta)
  change phaseWidth ((NetworkVertexCode.data r c b,TreeFraction.repr epsilon),delta)=
    CompanionUniformPhaseWidth.width (CompanionUniformPhaseWidth.data A s e (fun _ => 0) v) at hw
  dsimp only
  rw [hw]
  exact hc

theorem initialReserve_le (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0 < epsilon)
    (delta : TreeFraction.Fraction) :
    2*Fintype.card (Labels (ComputedCountingParameters.data hEK r c b hne epsilon he)) ≤
      bitCount ((NetworkVertexCode.data r c b,TreeFraction.repr epsilon),delta) := by
  have hc := (phaseWidth_covers hEK r c b hne epsilon he delta).2.2
  have hH := phases_pos hEK r c b hne epsilon he
  unfold bitCount
  rw [phaseCount_data hEK r c b hne epsilon he delta]
  exact hc.trans (by simpa only [Nat.one_mul] using Nat.mul_le_mul_right _ hH)

end
end ContingencyTables.CountingPositiveProgram

end OAI
