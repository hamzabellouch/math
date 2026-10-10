import OAI.Combinatorics.ContingencyTables.Counting.CountingComputedSettings

namespace OAI

/-! # The computed controls are the proven counting schedule -/

namespace ContingencyTables.CountingComputedSettings
open MatchingFPRAS CompanionFactorialApplication
open CountingPhaseParametersProgram
open scoped Classical
noncomputable section
variable {m n : ℕ}

lemma parameters_values (z : Input) (P W H L : ℕ)
    (hz : preliminary z=[P,W,H,0,0,0,L]) :
    parameters z=
      (let T := 4*CountingPhaseSchedule.observable P W*(H+P+L+5)
       let eta := CountingPhaseSchedule.tolerance H (TreeFraction.val z.2/2)
       ([P,W,H,T,CountingPhaseSchedule.observations P W H eta,
         CountingPhaseSchedule.returnCap P H T,L],CountingBaseProgram.half z.2)) := by
  unfold parameters basic
  rw [hz,basic_values,fillObservations_values,CountingBaseProgram.half_val]

lemma parameters_data (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0 < epsilon) :
    let A := ComputedCountingParameters.data hEK r c b hne epsilon he
    let s := ComputedCountingParameters.settings hEK r c b hne epsilon he
    parameters (NetworkVertexCode.data r c b,TreeFraction.repr epsilon)=
      ([Fintype.card (Labels A),A.W,s.H,CompanionTargetMixing.restartTime A s.H s.L,
        s.N,s.n,s.L],CountingBaseProgram.half (TreeFraction.repr epsilon)) := by
  let A := ComputedCountingParameters.data hEK r c b hne epsilon he
  let H := ComputedCountingParameters.phases r c b epsilon
  let L := ComputedCountingParameters.capacityBits r c b
  have hp : preliminary (NetworkVertexCode.data r c b,TreeFraction.repr epsilon)=
      [Fintype.card (Labels A),A.W,H,0,0,0,L] := by
    unfold preliminary
    rw [labelCount_data hEK r c b hne epsilon he,
      CountingTerminalProgram.cutoff_data r c b epsilon he,
      CountingTerminalProgram.phases_data r c b epsilon he,CountingBaseProgram.capacityBits_data]
    rfl
  rw [parameters_values _ _ _ _ _ hp,TreeFraction.val_repr he.le]
  have ht : 4*CountingPhaseSchedule.observable (Fintype.card (Labels A)) A.W*
      (H+Fintype.card (Labels A)+L+5)=CompanionTargetMixing.restartTime A H L := by
    simp only [CountingPhaseSchedule.observable,CompanionTargetMixing.restartTime,
      CompanionTrace.time,CompanionTrace.integerConstant]
    ring
  dsimp only
  rw [ht]
  rfl

lemma precision_data (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0 < epsilon) :
    precision (parameters (NetworkVertexCode.data r c b,TreeFraction.repr epsilon))=
      (ComputedCountingParameters.settings hEK r c b hne epsilon he).k := by
  rw [parameters_data hEK r c b hne epsilon he,precision_val,
    CountingBaseProgram.half_val,TreeFraction.val_repr he.le]
  rfl

lemma noise_data (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0 < epsilon) :
    TreeFraction.val (noise (parameters (NetworkVertexCode.data r c b,TreeFraction.repr epsilon)))=
      (ComputedCountingParameters.settings hEK r c b hne epsilon he).xi := by
  rw [parameters_data hEK r c b hne epsilon he,noise_val,
    CountingBaseProgram.half_val,TreeFraction.val_repr he.le]
  rfl

end
end ContingencyTables.CountingComputedSettings

end OAI
