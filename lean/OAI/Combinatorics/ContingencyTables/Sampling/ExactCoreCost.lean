import OAI.Combinatorics.ContingencyTables.Sampling.ExactCoreProgram

namespace OAI

/-! # Finite-prefix cost of the actual exact sampler control graph -/

namespace ContingencyTables.ExactCoreCost
open MatchingFPRAS MatchingFPRAS.TreeData MatchingFPRAS.TreeFunction
open MatchingFPRAS.TreeMachine (Env K encodeEnv)
open MatchingFPRAS.PhysicalStream MatchingFPRAS.OnlineStack
open ProfilePrograms DensePrograms ExactCoreProgram

noncomputable def retryCost (z : CompletionMargins) : ℕ :=
  OnlineIntegerRetry.stepCost ExactMatrixTrial.trialRealizer (exactMatrixInput z)

noncomputable def branchBudget (z : CompletionMargins) (N : ℕ) : ℕ :=
  exactOrdinaryRealizer.cost z+exactMatrixInputRealizer.cost z+N*retryCost z+
    2*TreeFunction.size (TreeTyped.encode z)+20

noncomputable def budget (z : CompletionMargins) (N : ℕ) : ℕ :=
  rareBranchRealizer.cost z+exactOrdinaryRealizer.cost z+exactMatrixInputRealizer.cost z+
    N*retryCost z+10*TreeFunction.size (TreeTyped.encode z)+50

/-- The failed endpoint is inside the actual retry subroutine. Its successful
endpoints have halted with the sampled matrix in the output register. -/
theorem prefix_correct_cost (z : CompletionMargins) (s : Data) (N : ℕ) :
    ∃ p,Executes program.code program.coin (output z s)
      (OnlineTree.initial program (TreeTyped.encode z) s) p ∧
      (∀ g : Option MatrixCode → ℚ,p.mean g=(prefixExperiment z N).mean g) ∧
      p.cost≤budget z N := by
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
  have rare : ∃ p,OnlinePartialCall.At instructions out (some .prepareRare)
      (env (TreeTyped.encode z) .nil s) p ∧
      (∀ g : Option MatrixCode → ℚ,p.mean g=(correctionPrefix z N).mean g) ∧
      p.cost≤exactMatrixInputRealizer.cost z+N*retryCost z+3 := by
    obtain ⟨u,hu,hum,huc⟩ := OnlineIntegerRetry.prefix_correct ExactMatrixTrial.trialRealizer
      (exactMatrixInput z) s N
    let v : Option MatrixCode → Experiment (Option MatrixCode) :=
      fun o => match o with | none => .done none | some X => .delay 1 (.done (some X))
    have hcall := OnlinePartialCall.partial_call instructions .retry
      ⟨_,.halt,rfl⟩ (env (TreeTyped.encode (exactMatrixInput z)) .nil s)
      (fun o => OnlineControl.cfg (OnlineIntegerRetry.instructions ExactMatrixTrial.trialRealizer)
        (OnlineIntegerRetry.output (exactMatrixInput z) s o).1
        (OnlineIntegerRetry.output (exactMatrixInput z) s o).2) u hu
    have hv : Executes (OnlineControl.code instructions) (OnlineControl.coins instructions) out
        (OnlineControl.cfg instructions (some .retry)
          (env (TreeTyped.encode (exactMatrixInput z)) .nil s))
        ((Experiment.delay 1 u).bind v) := by
      apply hcall.bind v out
      intro o
      cases o with
      | none => exact .done none
      | some X => exact halted X
    obtain ⟨p,hp,hpm,hpc⟩ := OnlinePartialCall.deterministicCall instructions out .prepareRare .retry
      exactMatrixInputRealizer.program rfl _ _ _ (exactMatrixInputRealizer.correct z s)
      ((Experiment.delay 1 u).bind v) hv
    refine ⟨p,hp,?_,?_⟩
    · intro g
      rw [hpm,Experiment.mean_bind]
      simp only [Experiment.mean]
      have he : (fun o => (v o).mean g)=g := by funext o; cases o <;> rfl
      rw [he,hum]
      rfl
    · have hv : ∀ o,(v o).cost≤1 := by intro o; cases o <;> simp only [v,Experiment.cost] <;> omega
      have hc := Experiment.cost_bind_le (Experiment.delay 1 u) v 1 hv
      simp only [Experiment.cost] at hc
      change u.cost≤N*retryCost z at huc
      omega
  have branch (b : Bool) : ∃ p,OnlinePartialCall.At instructions out (some .choose)
      (env (TreeTyped.encode b) .nil (.cons (TreeTyped.encode z) s)) p ∧
      (∀ g : Option MatrixCode → ℚ,p.mean g=
        (if b then correctionPrefix z N else (exactOrdinary z).map some).mean g) ∧
      p.cost≤branchBudget z N := by
    cases b with
    | false =>
      obtain ⟨p,hp,hpm,hpc⟩ := ordinary
      obtain ⟨v,hv,hvm,hvc⟩ := OnlinePartialCall.deterministicCall instructions out
        .ordinaryInput .ordinary (split 0 2 (by decide)) rfl _ _ _
        (split02 (TreeTyped.encode false) .nil (TreeTyped.encode z) s) p hp
      refine ⟨.delay 1 v,?_,(fun g => hvm g |>.trans (hpm g)),?_⟩
      · exact OnlinePartialCall.nilBranch instructions out .choose .ordinaryInput .rareInput 0 rfl _ rfl v hv
      · simp only [Experiment.cost] at ⊢
        have hb : TreeFunction.size (TreeTyped.encode false)≤3 := by decide
        unfold branchBudget
        omega
    | true =>
      obtain ⟨p,hp,hpm,hpc⟩ := rare
      obtain ⟨v,hv,hvm,hvc⟩ := OnlinePartialCall.deterministicCall instructions out
        .rareInput .prepareRare (split 0 2 (by decide)) rfl _ _ _
        (split02 (TreeTyped.encode true) .nil (TreeTyped.encode z) s) p hp
      refine ⟨.delay 1 v,?_,(fun g => hvm g |>.trans (hpm g)),?_⟩
      · exact OnlinePartialCall.consBranch instructions out .choose .ordinaryInput .rareInput 0 rfl _
          .nil .nil rfl v hv
      · simp only [Experiment.cost] at ⊢
        have hb : TreeFunction.size (TreeTyped.encode true)≤3 := by decide
        unfold branchBudget
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
    rw [hum,prefixExperiment,Experiment.mean_bind]
  · have hc := Experiment.cost_bind_le u v (branchBudget z N) hvc
    simp only [Experiment.cost] at hpc
    dsimp only [branchBudget,budget] at hc ⊢
    omega

end ContingencyTables.ExactCoreCost

end OAI
