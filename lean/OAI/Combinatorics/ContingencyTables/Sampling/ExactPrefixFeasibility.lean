import OAI.Combinatorics.ContingencyTables.Sampling.ExactPrefixLaw
import OAI.Combinatorics.ContingencyTables.Sampling.ExactMatrixLookup

namespace OAI

/-! # Feasibility is preserved on both branches and every finite retry prefix -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms MatchingFPRAS.PhysicalStream
open scoped BigOperators Classical
noncomputable section

variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
attribute [local irreducible] exactOrdinary correctionPrefix exactMatrixInput
  ExactCoreProgram.prefixExperiment scheduledTableDraw ExactIntegerOnline.trial
  scheduledResidualCounts originalCandidates

def FeasibleCode (X : MatrixCode) : Prop := ∃ T : Table r c,X=matrixCode T.val

def FeasibleOutcome (o : Option MatrixCode) : Prop := o.elim True (FeasibleCode r c)

lemma exactOrdinary_feasible (htotal : (∑ i,r i)=∑ j,c j) :
    (exactOrdinary (List.ofFn r,List.ofFn c)).All (FeasibleCode r c) := by
  rw [Experiment.all_indicator,exactOrdinary_mean r c htotal]
  have he (bits : Bits (finiteSamplerBits r c (2*correctionPrecision r c))) :
      (if FeasibleCode r c (matrixCode (scheduledTableDraw r c htotal
        (2*correctionPrecision r c) bits).val) then (0:ℚ) else 1)=0 :=
    ite_eq_left ⟨_,rfl⟩
  simp_rw [he]
  exact average_const _ _

lemma exactTrial_feasible (htotal : (∑ i,r i)=∑ j,c j) :
    (ExactMatrixTrial.trial (exactMatrixInput (List.ofFn r,List.ofFn c))).All
      (FeasibleOutcome r c) := by
  rw [exactMatrixInput_code r c htotal,ExactMatrixTrial.trial,Experiment.all_map]
  apply (Experiment.all_true _).mono
  intro o _
  cases o with
  | none => trivial
  | some i =>
    exact ExactMatrixTrial.lookup_feasible r c (GreedyFeasibleTable.table r c htotal) i

lemma correctionPrefix_feasible (htotal : (∑ i,r i)=∑ j,c j) (N : ℕ) :
    (correctionPrefix (List.ofFn r,List.ofFn c) N).All (FeasibleOutcome r c) := by
  unfold correctionPrefix
  induction N with
  | zero => trivial
  | succ N ih =>
    rw [OnlineIntegerRetry.prefixExperiment,Experiment.all_bind]
    apply (exactTrial_feasible r c htotal).mono
    intro o ho
    cases o with
    | none => exact ih
    | some X => exact ho

lemma exactPrefix_feasible (htotal : (∑ i,r i)=∑ j,c j) (N : ℕ) :
    (ExactCoreProgram.prefixExperiment (List.ofFn r,List.ofFn c) N).All (FeasibleOutcome r c) := by
  rw [ExactCoreProgram.prefixExperiment,Experiment.all_bind]
  apply (Experiment.all_true _).mono
  intro rare _
  cases rare with
  | false =>
    rw [ite_eq_right Bool.false_ne_true,Experiment.all_map]
    exact exactOrdinary_feasible r c htotal
  | true => exact correctionPrefix_feasible r c htotal N

end
end ContingencyTables.SmallGraphProfiles

end OAI
