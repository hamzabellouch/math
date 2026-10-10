import OAI.Combinatorics.ContingencyTables.Counting.CountingDirectSemantics
import OAI.Combinatorics.ContingencyTables.Transport.FiniteObservableReindex
import OAI.Combinatorics.ContingencyTables.Transport.FinitePaddedAverage

namespace OAI

/-! # Exact law of the executed direct counting estimator -/
namespace ContingencyTables.CountingDirectProgram
open MatchingFPRAS CompanionFactorialApplication CompanionOracleDensity GridBoundary
open CommonBasesFPRAS FiniteObservableTransport
open scoped Classical
noncomputable section
variable {m n : ℕ}

def modelContext (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0 < epsilon) :
    RootedEstimatorLayoutProgram.Context :=
  let A := ComputedCountingParameters.data hEK r c b hne epsilon he
  let C := ComputedCountingParameters.coefficient r c b epsilon
  let K := ComputedCountingParameters.binCount r c b epsilon
  RootedEstimatorMedianProgram.context A C K (ComputedCountingParameters.phases r c b epsilon)
    ((epsilon/2)/2) (fun _ => 0)
    (CountingPreparedState.start A K (ComputedCountingParameters.binCount_pos r c b epsilon he))

def modelWidth (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0 < epsilon) (delta : ℚ) : ℕ :=
  repetitionCount delta*RootedEstimatorLayoutProgram.wordWidth (modelContext hEK r c b hne epsilon he)

def modelValue (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0 < epsilon)
    (delta : ℚ) (bits : List Bool) : ℚ :=
  TreeFraction.val (RootedEstimatorMedianProgram.output
    ((modelContext hEK r c b hne epsilon he,repetitionCount delta),
      ((List.replicate (degree r c b epsilon) false,List.replicate (depth r c b epsilon) false),bits)))

attribute [local irreducible] modelContext modelWidth modelValue
attribute [local irreducible] ComputedCountingParameters.data ComputedCountingParameters.coefficient
attribute [local irreducible] ComputedCountingParameters.phases ComputedCountingParameters.binCount
attribute [local irreducible] ComputedCountingZero.zeroEstimate ComputedCountingZero.zeroBits

lemma modelWidth_eq (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0 < epsilon) (delta : ℚ) :
    modelWidth hEK r c b hne epsilon he delta=ComputedCountingZero.zeroBits hEK r c b hne epsilon he delta := by
  unfold modelWidth modelContext RootedEstimatorMedianProgram.context
  rw [RootedEstimatorWordProgram.scheduledWordWidth]
  unfold ComputedCountingZero.zeroBits medianEstimatorBits
  rw [←ComputedCountingParameters.phases_final hEK r c b hne epsilon he]

def referenceBits (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0 < epsilon) (delta : ℚ) : ℕ :=
  medianEstimatorBits (ComputedCountingParameters.data hEK r c b hne epsilon he)
    (ComputedCountingParameters.coefficient r c b epsilon) (ComputedCountingParameters.binCount r c b epsilon)
    (ComputedCountingParameters.phases r c b epsilon) ((epsilon/2)/2) delta

def reference (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0 < epsilon) (delta : ℚ)
    (bits : Fin (referenceBits hEK r c b hne epsilon he delta)→Bool) : ℚ :=
  RootedOracleDensity.medianEstimate (ComputedCountingParameters.data hEK r c b hne epsilon he)
    (ComputedCountingWords.root hEK r c b hne epsilon he) (ComputedCountingParameters.coefficient r c b epsilon)
    (fun _ => 0) (ComputedCountingParameters.binCount r c b epsilon)
    (ComputedCountingParameters.binCount_pos r c b epsilon he)
    (ComputedCountingParameters.cutoff_eq hEK r c b hne epsilon he).ge
    (ComputedCountingParameters.phases r c b epsilon) ((epsilon/2)/2) delta
    (ComputedCountingParameters.start hEK r c b hne epsilon he) bits

attribute [local irreducible] referenceBits reference

lemma native_sameLaw (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ) (he : 0 < epsilon) :
    SameLaw (fun bits : Fin (modelWidth hEK r c b hne epsilon he delta)→Bool =>
      modelValue hEK r c b hne epsilon he delta (List.ofFn bits))
      (reference hEK r c b hne epsilon he delta) := by
  let A := ComputedCountingParameters.data hEK r c b hne epsilon he
  let C := ComputedCountingParameters.coefficient r c b epsilon
  let K := ComputedCountingParameters.binCount r c b epsilon
  let H := ComputedCountingParameters.phases r c b epsilon
  have hs := RootedEstimatorMedianProgram.sameLaw A C K H
    (ComputedCountingParameters.coefficient_pos r c b epsilon he)
    (ComputedCountingParameters.phases_height hEK r c b hne epsilon he).le
    (ComputedCountingParameters.binCount_pos r c b epsilon he)
    (ComputedCountingParameters.cutoff_eq hEK r c b hne epsilon he).ge
    (ComputedCountingParameters.binCount_cast hEK r c b hne epsilon he)
    ((epsilon/2)/2) delta (by positivity) (fun _ => 0) (fun _ => Nat.zero_le _)
    (CountingPreparedState.start A K (ComputedCountingParameters.binCount_pos r c b epsilon he))
    (List.replicate (degree r c b epsilon) false) (List.replicate (depth r c b epsilon) false)
    (by rw [List.length_replicate]; rfl) (by rw [List.length_replicate]; rfl)
  dsimp only [A,C,K,H] at hs
  rw [CountingPreparedState.start_transport hEK r c b hne epsilon he] at hs
  unfold RootedEstimatorMedianProgram.value at hs
  unfold modelWidth modelValue modelContext reference referenceBits ComputedCountingWords.root
  exact hs

lemma reference_sameLaw (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ) (he : 0 < epsilon) :
    SameLaw (reference hEK r c b hne epsilon he delta)
      (ComputedCountingZero.zeroEstimate hEK r c b hne epsilon he delta) := by
  unfold reference referenceBits ComputedCountingZero.zeroEstimate ComputedCountingZero.zeroBits
  rw [←ComputedCountingParameters.phases_final hEK r c b hne epsilon he]
  intro phi
  rfl

lemma model_sameLaw (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ) (he : 0 < epsilon) :
    SameLaw (fun bits : Fin (modelWidth hEK r c b hne epsilon he delta)→Bool =>
      modelValue hEK r c b hne epsilon he delta (List.ofFn bits))
      (ComputedCountingZero.zeroEstimate hEK r c b hne epsilon he delta) := by
  intro phi
  exact (native_sameLaw hEK r c b hne epsilon delta he phi).trans
    (reference_sameLaw hEK r c b hne epsilon delta he phi)

lemma output_model (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ)
    (he : 0 < epsilon) (hd : 0 < delta) (N : ℕ)
    (hwidth : modelWidth hEK r c b hne epsilon he delta ≤ N)
    (hdegree : degree r c b epsilon ≤ N) (hdepth : depth r c b epsilon ≤ N)
    (bits : Fin N→Bool) :
    TreeFraction.val (output (request r c b epsilon delta,List.ofFn bits))=
      modelValue hEK r c b hne epsilon he delta
        (List.ofFn (FirstSuccess.prefixWord hwidth bits)) := by
  have hw : wordWidth (request r c b epsilon delta,List.ofFn bits)=modelWidth hEK r c b hne epsilon he delta :=
    (wordWidth_data hEK r c b hne epsilon delta he hd _).trans (modelWidth_eq hEK r c b hne epsilon he delta).symm
  have hc : context (request r c b epsilon delta,List.ofFn bits)=modelContext hEK r c b hne epsilon he :=
    by
      unfold modelContext
      exact context_data hEK r c b hne epsilon delta he _
  have hr : repeats (request r c b epsilon delta,List.ofFn bits)=repetitionCount delta := by
    change FractionRepetitionProgram.count (TreeFraction.repr delta)=_
    rw [FractionRepetitionProgram.count_val,TreeFraction.val_repr hd.le]
  have hm := markers_data hEK r c b hne epsilon delta he N hdegree hdepth bits
  unfold output medianInput config sampleBits
  rw [hc,hr,hm,hw,BinVectorProgram.take_ofFn_prefix hwidth]
  unfold modelValue
  rfl

lemma sameLaw (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ)
    (he : 0 < epsilon) (hd : 0 < delta) :
    SameLaw (fun bits : Fin (budget (request r c b epsilon delta))→Bool =>
      TreeFraction.val (output (request r c b epsilon delta,List.ofFn bits)))
      (ComputedCountingZero.zeroEstimate hEK r c b hne epsilon he delta) := by
  have hbudget := budget_data hEK r c b hne epsilon delta he hd
  have hwidth : modelWidth hEK r c b hne epsilon he delta ≤ budget (request r c b epsilon delta) := by
    rw [modelWidth_eq,hbudget]
    omega
  have hdegree : degree r c b epsilon ≤ budget (request r c b epsilon delta) := by omega
  have hdepth : depth r c b epsilon ≤ budget (request r c b epsilon delta) := by omega
  intro phi
  simp_rw [output_model hEK r c b hne epsilon delta he hd _ hwidth hdegree hdepth]
  exact (FairBits.padded_equiv_average hwidth (Equiv.refl _) (fun bits =>
    phi (modelValue hEK r c b hne epsilon he delta (List.ofFn bits)))).trans
    (model_sameLaw hEK r c b hne epsilon delta he phi)

end
end ContingencyTables.CountingDirectProgram

end OAI
