import OAI.Combinatorics.ContingencyTables.Counting.CountingDirectProgram
import OAI.Combinatorics.ContingencyTables.Rooted.RootedOracleConfigSemantics
import OAI.Combinatorics.ContingencyTables.Counting.ComputedCountingZero

namespace OAI

/-! # The direct binary evaluator uses the original counting parameters -/
namespace ContingencyTables.CountingDirectProgram
open MatchingFPRAS CompanionFactorialApplication GridBoundary CompanionOracleDensity
open scoped Classical
noncomputable section
variable {m n : ℕ}

def request (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ) (epsilon delta : ℚ) : Request :=
  ((NetworkVertexCode.data r c b,TreeFraction.repr epsilon),TreeFraction.repr delta)

lemma accuracy_value (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (epsilon delta : ℚ) (he : 0 < epsilon) (bits : List Bool) :
    TreeFraction.val (accuracy (request r c b epsilon delta,bits))=(epsilon/2)/2 := by
  change TreeFraction.val (CountingBaseProgram.half (CountingBaseProgram.half (TreeFraction.repr epsilon)))=_
  rw [CountingBaseProgram.half_val,CountingBaseProgram.half_val,TreeFraction.val_repr he.le]

lemma oracleInput_data (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ) (he : 0 < epsilon)
    (bits : List Bool) :
    let A := ComputedCountingParameters.data hEK r c b hne epsilon he
    let C := ComputedCountingParameters.coefficient r c b epsilon
    let K := ComputedCountingParameters.binCount r c b epsilon
    let H := ComputedCountingParameters.phases r c b epsilon
    oracleInput (request r c b epsilon delta,bits)=
      RootedOracleConfigProgram.data A C K H
        (accuracy (request r c b epsilon delta,bits)) (fun _ => 0)
        (CountingPreparedState.start A K (ComputedCountingParameters.binCount_pos r c b epsilon he))
        (bits.map (fun _ => false)) := by
  dsimp only
  unfold oracleInput request
  rw [CountingPreparedState.state_data hEK r c b hne epsilon he,
    CountingTerminalProgram.phases_data r c b epsilon he]
  rfl

lemma context_data (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ) (he : 0 < epsilon)
    (bits : List Bool) :
    let A := ComputedCountingParameters.data hEK r c b hne epsilon he
    let C := ComputedCountingParameters.coefficient r c b epsilon
    let K := ComputedCountingParameters.binCount r c b epsilon
    let H := ComputedCountingParameters.phases r c b epsilon
    context (request r c b epsilon delta,bits)=
      RootedEstimatorMedianProgram.context A C K H ((epsilon/2)/2) (fun _ => 0)
        (CountingPreparedState.start A K (ComputedCountingParameters.binCount_pos r c b epsilon he)) := by
  dsimp only
  change RootedOracleConfigProgram.context (oracleInput (request r c b epsilon delta,bits))=_
  rw [oracleInput_data hEK r c b hne epsilon delta he bits,
    RootedOracleConfigProgram.context_data,accuracy_value r c b epsilon delta he bits]

lemma wordWidth_data (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ) (he : 0 < epsilon) (hd : 0 < delta)
    (bits : List Bool) :
    wordWidth (request r c b epsilon delta,bits)=
      ComputedCountingZero.zeroBits hEK r c b hne epsilon he delta := by
  have hr : repeats (request r c b epsilon delta,bits)=CommonBasesFPRAS.repetitionCount delta := by
    change FractionRepetitionProgram.count (TreeFraction.repr delta)=_
    rw [FractionRepetitionProgram.count_val,TreeFraction.val_repr hd.le]
  rw [wordWidth,hr,contextWidth]
  rw [oracleInput_data hEK r c b hne epsilon delta he bits,
    RootedOracleConfigProgram.contextWidth,RootedOracleConfigProgram.context_data,
    accuracy_value r c b epsilon delta he bits]
  rw [RootedEstimatorMedianProgram.context,RootedEstimatorWordProgram.scheduledWordWidth]
  unfold ComputedCountingZero.zeroBits medianEstimatorBits
  rw [←ComputedCountingParameters.phases_final hEK r c b hne epsilon he]

def degree (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ) (epsilon : ℚ) : ℕ :=
  PowerOfTwoApproximation.rootDegree (roundingTolerance
    (innerTolerance (((epsilon/2)/2)/2) (ComputedCountingParameters.phases r c b epsilon)))
def depth (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ) (epsilon : ℚ) : ℕ :=
  PowerOfTwoApproximation.depth (roundingTolerance
    (innerTolerance (((epsilon/2)/2)/2) (ComputedCountingParameters.phases r c b epsilon)))

lemma degree_data (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ) (he : 0 < epsilon)
    (bits : List Bool) :
    RootedOracleConfigProgram.rootDegree (oracleInput (request r c b epsilon delta,bits))=
      degree r c b epsilon := by
  rw [oracleInput_data hEK r c b hne epsilon delta he bits,
    RootedOracleConfigProgram.rootDegree_data,accuracy_value r c b epsilon delta he bits]
  rfl

lemma depth_data (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ) (he : 0 < epsilon)
    (bits : List Bool) :
    RootedOracleConfigProgram.depth (oracleInput (request r c b epsilon delta,bits))=
      depth r c b epsilon := by
  rw [oracleInput_data hEK r c b hne epsilon delta he bits,
    RootedOracleConfigProgram.depth_data,accuracy_value r c b epsilon delta he bits]
  rfl

lemma budget_data (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ)
    (he : 0 < epsilon) (hd : 0 < delta) :
    budget (request r c b epsilon delta)=
      ComputedCountingZero.zeroBits hEK r c b hne epsilon he delta+degree r c b epsilon+depth r c b epsilon := by
  unfold budget padding empty
  rw [wordWidth_data hEK r c b hne epsilon delta he hd [],
    degree_data hEK r c b hne epsilon delta he [],depth_data hEK r c b hne epsilon delta he []]
  omega

lemma markers_data (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ) (he : 0 < epsilon)
    (N : ℕ) (hdegree : degree r c b epsilon ≤ N) (hdepth : depth r c b epsilon ≤ N)
    (bits : Fin N→Bool) :
    markers (request r c b epsilon delta,List.ofFn bits)=
      (List.replicate (degree r c b epsilon) false,List.replicate (depth r c b epsilon) false) := by
  change RootedOracleConfigProgram.markers
    (oracleInput (request r c b epsilon delta,List.ofFn bits))=_
  rw [RootedOracleConfigProgram.markers,
    degree_data hEK r c b hne epsilon delta he (List.ofFn bits),
    depth_data hEK r c b hne epsilon delta he (List.ofFn bits)]
  simp only [oracleInput,reserve,List.map_ofFn,Function.comp_def,List.ofFn_const,
    List.take_replicate,min_eq_left hdegree,min_eq_left hdepth]

lemma sampleBits_data (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ)
    (he : 0 < epsilon) (hd : 0 < delta) (N : ℕ)
    (hwidth : ComputedCountingZero.zeroBits hEK r c b hne epsilon he delta ≤ N) (bits : Fin N→Bool) :
    sampleBits (request r c b epsilon delta,List.ofFn bits)=List.ofFn (FirstSuccess.prefixWord hwidth bits) := by
  rw [sampleBits,wordWidth_data hEK r c b hne epsilon delta he hd]
  exact BinVectorProgram.take_ofFn_prefix hwidth bits

end
end ContingencyTables.CountingDirectProgram

end OAI
