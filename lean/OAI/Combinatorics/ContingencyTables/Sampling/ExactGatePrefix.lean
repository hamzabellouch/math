import OAI.Combinatorics.ContingencyTables.Sampling.ExactCoreCost
import OAI.Combinatorics.ContingencyTables.Sampling.PhysicalPartialSequence

namespace OAI

/-! # A cheap prefix ending before rare-branch tabulation -/

namespace ContingencyTables.ExactGatePrefix
open MatchingFPRAS MatchingFPRAS.TreeData MatchingFPRAS.TreeFunction
open MatchingFPRAS.TreeMachine (Env K encodeEnv)
open MatchingFPRAS.PhysicalStream MatchingFPRAS.OnlineStack
open ProfilePrograms DensePrograms ExactCoreProgram

noncomputable def output (z : CompletionMargins) (s : Data) :
    Option MatrixCode → OnlinePartialCall.Config instructions
  | none => OnlineControl.cfg instructions (some .prepareRare) (env (TreeTyped.encode z) .nil s)
  | some X => OnlineControl.cfg instructions none (env (TreeTyped.encode X) .nil s)

def experiment (z : CompletionMargins) : Experiment (Option MatrixCode) :=
  (rareBranch z).bind (fun b => if b then .done none else (exactOrdinary z).map some)

noncomputable def budget (z : CompletionMargins) : ℕ :=
  rareBranchRealizer.cost z+exactOrdinaryRealizer.cost z+10*TreeFunction.size (TreeTyped.encode z)+50

/-- The rare branch is selected but its potentially large tabulation has
not started at the failure endpoint of this bounded prefix. -/
theorem prefix_correct_cost (z : CompletionMargins) (s : Data) :
    ∃ p,Executes program.code program.coin (output z s)
      (OnlineTree.initial program (TreeTyped.encode z) s) p ∧
      (∀ g : Option MatrixCode → ℚ,p.mean g=(experiment z).mean g) ∧ p.cost≤budget z := by
  let out := output z s
  have halted (X : MatrixCode) :
      OnlinePartialCall.At instructions out (some .halt) (env (TreeTyped.encode X) .nil s)
        (.delay 1 (.done (some X))) :=
    OnlinePartialCall.halt instructions out .halt rfl (some X) _ rfl
  have ordinary : ∃ p,OnlinePartialCall.At instructions out (some .ordinary)
      (env (TreeTyped.encode z) .nil s) p ∧
      (∀ g : Option MatrixCode → ℚ,p.mean g=((exactOrdinary z).map some).mean g) ∧
      p.cost≤exactOrdinaryRealizer.cost z+2 := by
    obtain ⟨u,hu,hum,huc⟩ := exactOrdinaryRealizer.correct z s
    refine ⟨.delay 1 (u.bind (fun X => .delay 1 (.done (some X)))),?_,?_,?_⟩
    · exact OnlinePartialCall.call instructions out .ordinary .halt exactOrdinaryRealizer.program
        rfl _ (fun X => env (TreeTyped.encode X) .nil s) u hu _ halted
    · intro g
      simp only [Experiment.mean,Experiment.mean_bind,Experiment.mean_map]
      exact hum _
    · have hc := Experiment.cost_bind_le u (fun X => .delay 1 (.done (some X))) 1
        (by intro X; rfl)
      simp only [Experiment.cost] at hc ⊢
      omega
  have branch (b : Bool) : ∃ p,OnlinePartialCall.At instructions out (some .choose)
      (env (TreeTyped.encode b) .nil (.cons (TreeTyped.encode z) s)) p ∧
      (∀ g : Option MatrixCode → ℚ,p.mean g=
        (if b then (.done none : Experiment (Option MatrixCode)) else (exactOrdinary z).map some).mean g) ∧
      p.cost≤exactOrdinaryRealizer.cost z+2*TreeFunction.size (TreeTyped.encode z)+20 := by
    cases b with
    | false =>
      obtain ⟨p,hp,hpm,hpc⟩ := ordinary
      obtain ⟨v,hv,hvm,hvc⟩ := OnlinePartialCall.deterministicCall instructions out
        .ordinaryInput .ordinary (split 0 2 (by decide)) rfl _ _ _
        (split02 (TreeTyped.encode false) .nil (TreeTyped.encode z) s) p hp
      refine ⟨.delay 1 v,?_,(fun g => (hvm g).trans (hpm g)),?_⟩
      · exact OnlinePartialCall.nilBranch instructions out .choose .ordinaryInput .rareInput 0 rfl _ rfl v hv
      · have hb : TreeFunction.size (TreeTyped.encode false)≤3 := by decide
        simp only [Experiment.cost]
        omega
    | true =>
      have hp : OnlinePartialCall.At instructions out (some .prepareRare)
          (env (TreeTyped.encode z) .nil s) (.done none) := .done none
      obtain ⟨v,hv,hvm,hvc⟩ := OnlinePartialCall.deterministicCall instructions out
        .rareInput .prepareRare (split 0 2 (by decide)) rfl _ _ _
        (split02 (TreeTyped.encode true) .nil (TreeTyped.encode z) s) (.done none) hp
      refine ⟨.delay 1 v,?_,hvm,?_⟩
      · exact OnlinePartialCall.consBranch instructions out .choose .ordinaryInput .rareInput 0 rfl _
          .nil .nil rfl v hv
      · have hb : TreeFunction.size (TreeTyped.encode true)≤3 := by decide
        simp only [Experiment.cost] at hvc ⊢
        omega
  choose v hv hvm hvc using branch
  obtain ⟨u,hu,hum,huc⟩ := rareBranchRealizer.correct z (.cons (TreeTyped.encode z) s)
  have hgate := OnlinePartialCall.call instructions out .gate .choose rareBranchRealizer.program
    rfl _ (fun b => env (TreeTyped.encode b) .nil (.cons (TreeTyped.encode z) s)) u hu v hv
  obtain ⟨p,hp,hpm,hpc⟩ := OnlinePartialCall.deterministicCall instructions out .prepare .gate
    OnlineIntegerRetry.prepareProc rfl _ _ _ (OnlineIntegerRetry.prepare_exec (TreeTyped.encode z) s)
    (.delay 1 (u.bind v)) hgate
  refine ⟨p,hp,?_,?_⟩
  · intro g
    rw [hpm]
    simp only [Experiment.mean,Experiment.mean_bind]
    simp_rw [hvm]
    rw [hum,experiment,Experiment.mean_bind]
  · have hc := Experiment.cost_bind_le u v
      (exactOrdinaryRealizer.cost z+2*TreeFunction.size (TreeTyped.encode z)+20) hvc
    simp only [Experiment.cost] at hpc
    unfold budget
    omega

lemma failure (z : CompletionMargins) :
    (experiment z).mean (fun o => if o=none then 1 else 0)=1/(2:ℚ)^(exactPrecision z) := by
  rw [experiment,Experiment.mean_bind]
  have he : (fun b : Bool => (if b then (.done none : Experiment (Option MatrixCode))
      else (exactOrdinary z).map some).mean (fun o => if o=none then 1 else 0))=
      (fun b => if b then 1 else 0) := by
    funext b
    cases b with
    | true => rfl
    | false =>
      simp only [Bool.false_eq_true,ite_false,Experiment.mean_map,Option.some_ne_none]
      exact PhysicalPartialSequence.mean_const _ _
  rw [he,rareBranch_probability]

end ContingencyTables.ExactGatePrefix

end OAI
