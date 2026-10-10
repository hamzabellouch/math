import OAI.Combinatorics.ContingencyTables.Sampling.ExactTypedProgram
import OAI.Combinatorics.ContingencyTables.Sampling.ExactGatePrefix

namespace OAI

/-! # Parsing and printing around the cheap pre-tabulation prefix -/

namespace ContingencyTables.ExactGateTyped
open MatchingFPRAS MatchingFPRAS.TreeData MatchingFPRAS.TreeFunction
open MatchingFPRAS.TreeMachine (K encodeEnv)
open MatchingFPRAS.PhysicalStream MatchingFPRAS.OnlineStack
open ProfilePrograms DensePrograms ExactTypedProgram

noncomputable def printedOutput (z : CompletionMargins) (s : Data) :
    Option MatrixCode → OnlineTree.StoreCfg printedProgram
  | none => StackComposition.mapCfg Sum.inl (some (Sum.inr default)) (ExactGatePrefix.output z s none)
  | some X => OnlineTree.final printedProgram (TreeTyped.encode (GreedyFeasibleTable.printMatrix X)) s

noncomputable def output (as : List Symbol) (s : Data) (o : Option MatrixCode) :
    OnlineTree.StoreCfg program := StackComposition.mapCfg Sum.inr none
      (printedOutput (exactParsedMargins as) s o)

theorem printed_correct_cost (z : CompletionMargins) (s : Data) (B : ℕ)
    (hB : (ExactGatePrefix.experiment z).All
      (fun o => o.elim 0 GreedyFeasibleTable.printMatrixRealizer.cost≤B)) :
    ∃ p,Executes printedProgram.code printedProgram.coin (printedOutput z s)
      (OnlineTree.initial printedProgram (TreeTyped.encode z) s) p ∧
      (∀ g : Option MatrixCode → ℚ,p.mean g=(ExactGatePrefix.experiment z).mean g) ∧
      p.cost≤ExactGatePrefix.budget z+B := by
  obtain ⟨p,hp,hpm,hpc⟩ := ExactGatePrefix.prefix_correct_cost z s
  have hp' := hp.relabel printedProgram.code printedProgram.coin Sum.inl
    (some (Sum.inr default)) (fun _ => rfl) (fun _ => rfl)
  have next (o : Option MatrixCode) : ∃ q,
      Executes printedProgram.code printedProgram.coin (printedOutput z s)
        (StackComposition.mapCfg Sum.inl (some (Sum.inr default)) (ExactGatePrefix.output z s o)) q ∧
      (∀ g : Option MatrixCode → ℚ,q.mean g=g o) ∧
      q.cost≤o.elim 0 GreedyFeasibleTable.printMatrixRealizer.cost := by
    cases o with
    | none => exact ⟨.done none,.done none,(fun _ => rfl),le_rfl⟩
    | some X =>
      obtain ⟨n,hnb,hn⟩ := GreedyFeasibleTable.printMatrixRealizer.correct X s
      obtain ⟨q,hq,hqm,hqc⟩ := Executes.of_run GreedyFeasibleTable.printMatrixRealizer.program.code n
        (OnlineTree.initial (OnlineProc.deterministic GreedyFeasibleTable.printMatrixRealizer.program)
          (TreeTyped.encode X) s) none (encodeEnv (env
          (TreeTyped.encode (GreedyFeasibleTable.printMatrix X)) .nil s)) hn
      have hq' := hq.relabel printedProgram.code printedProgram.coin Sum.inr none
        (fun _ => rfl) (fun _ => rfl)
      refine ⟨q.bind (fun _ => .done (some X)),?_,?_,?_⟩
      · exact hq'.bind _ _ (fun _ => .done (some X))
      · intro g
        simpa only [Experiment.mean_bind,Experiment.mean] using hqm (fun _ => g (some X))
      · have hc := Experiment.cost_bind_le q (fun _ => .done (some X)) 0 (fun _ => le_rfl)
        simp only [Option.elim_some,Nat.add_zero] at hc ⊢
        exact hc.trans (hqc.trans hnb)
  choose q hq hqm hqc using next
  refine ⟨p.bind q,hp'.bind q _ hq,?_,?_⟩
  · intro g
    rw [Experiment.mean_bind]
    simp_rw [hqm]
    exact hpm g
  · have hall := Experiment.all_of_mean_eq hpm _ hB
    exact (Experiment.cost_bind_le_of_all p q B (hall.mono
      (fun o ho => (hqc o).trans ho))).trans (Nat.add_le_add_right hpc B)

theorem prefix_correct_cost (as : List Symbol) (s : Data) (B : ℕ)
    (hB : (ExactGatePrefix.experiment (exactParsedMargins as)).All
      (fun o => o.elim 0 GreedyFeasibleTable.printMatrixRealizer.cost≤B)) :
    ∃ p,Executes program.code program.coin (output as s)
      (OnlineTree.initial program (TreeTyped.encode as) s) p ∧
      (∀ g : Option MatrixCode → ℚ,
        p.mean g=(ExactGatePrefix.experiment (exactParsedMargins as)).mean g) ∧
      p.cost≤exactParsedMarginsRealizer.cost as+ExactGatePrefix.budget (exactParsedMargins as)+B := by
  obtain ⟨p,hp,hpm,hpc⟩ := printed_correct_cost (exactParsedMargins as) s B hB
  have hp' := hp.relabel program.code program.coin Sum.inr none (fun _ => rfl) (fun _ => rfl)
  obtain ⟨n,hnb,hn⟩ := exactParsedMarginsRealizer.correct as s
  obtain ⟨u,hu,hum,huc⟩ := Executes.of_run exactParsedMarginsRealizer.program.code n
    (OnlineTree.initial (OnlineProc.deterministic exactParsedMarginsRealizer.program)
      (TreeTyped.encode as) s) none (encodeEnv (env (TreeTyped.encode (exactParsedMargins as)) .nil s)) hn
  have hu' := hu.relabel program.code program.coin Sum.inl
    (some (Sum.inr default)) (fun _ => rfl) (fun _ => rfl)
  refine ⟨u.bind (fun _ => p),hu'.bind _ _ (fun _ => hp'),?_,?_⟩
  · intro g
    rw [Experiment.mean_bind,hum]
    exact hpm g
  · have hc := Experiment.cost_bind_le u (fun _ => p) p.cost (fun _ => le_rfl)
    omega

end ContingencyTables.ExactGateTyped

end OAI
