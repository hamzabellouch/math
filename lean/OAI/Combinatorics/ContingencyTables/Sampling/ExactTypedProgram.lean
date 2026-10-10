import OAI.Combinatorics.ContingencyTables.Sampling.ExactCoreProgram
import OAI.Combinatorics.ContingencyTables.Machines.LiteralProgram

namespace OAI

/-! # Parsing and printing around the same unbounded exact core -/

namespace ContingencyTables.ExactTypedProgram
open MatchingFPRAS MatchingFPRAS.TreeData MatchingFPRAS.TreeFunction
open MatchingFPRAS.TreeMachine (K encodeEnv)
open MatchingFPRAS.PhysicalStream MatchingFPRAS.OnlineStack
open ProfilePrograms DensePrograms

noncomputable def printedProgram : OnlineProc.Proc (K Reg) :=
  OnlineProc.seq ExactCoreProgram.program
    (OnlineProc.deterministic GreedyFeasibleTable.printMatrixRealizer.program)

noncomputable def printedOutput (z : CompletionMargins) (s : Data) :
    Option MatrixCode → OnlineTree.StoreCfg printedProgram
  | none => StackComposition.mapCfg Sum.inl (some (Sum.inr default)) (ExactCoreProgram.output z s none)
  | some X => OnlineTree.final printedProgram (TreeTyped.encode (GreedyFeasibleTable.printMatrix X)) s

theorem printed_correct (z : CompletionMargins) (s : Data) (N : ℕ) :
    ∃ p,Executes printedProgram.code printedProgram.coin (printedOutput z s)
      (OnlineTree.initial printedProgram (TreeTyped.encode z) s) p ∧
      ∀ g : Option MatrixCode → ℚ,p.mean g=(ExactCoreProgram.prefixExperiment z N).mean g := by
  obtain ⟨p,hp,hpm⟩ := ExactCoreProgram.prefix_correct z s N
  have hp' := hp.relabel printedProgram.code printedProgram.coin Sum.inl
    (some (Sum.inr default)) (fun _ => rfl) (fun _ => rfl)
  have next (o : Option MatrixCode) : ∃ q,
      Executes printedProgram.code printedProgram.coin (printedOutput z s)
        (StackComposition.mapCfg Sum.inl (some (Sum.inr default)) (ExactCoreProgram.output z s o)) q ∧
      ∀ g : Option MatrixCode → ℚ,q.mean g=g o := by
    cases o with
    | none => exact ⟨.done none,.done none,fun _ => rfl⟩
    | some X =>
      obtain ⟨n,_,hn⟩ := GreedyFeasibleTable.printMatrixRealizer.correct X s
      obtain ⟨q,hq,hqm,_⟩ := Executes.of_run GreedyFeasibleTable.printMatrixRealizer.program.code n
        (OnlineTree.initial (OnlineProc.deterministic GreedyFeasibleTable.printMatrixRealizer.program)
          (TreeTyped.encode X) s) none (encodeEnv (env
          (TreeTyped.encode (GreedyFeasibleTable.printMatrix X)) .nil s)) hn
      have hq' := hq.relabel printedProgram.code printedProgram.coin Sum.inr none
        (fun _ => rfl) (fun _ => rfl)
      refine ⟨q.bind (fun _ => .done (some X)),?_,?_⟩
      · exact hq'.bind _ _ (fun _ => .done (some X))
      · intro g
        simpa only [Experiment.mean_bind,Experiment.mean] using hqm (fun _ => g (some X))
  choose q hq hqm using next
  refine ⟨p.bind q,hp'.bind q _ hq,?_⟩
  intro g
  rw [Experiment.mean_bind]
  simp_rw [hqm]
  exact hpm g

noncomputable def program : OnlineProc.Proc (K Reg) :=
  OnlineProc.seq (OnlineProc.deterministic exactParsedMarginsRealizer.program) printedProgram

noncomputable def output (as : List Symbol) (s : Data) (o : Option MatrixCode) :
    OnlineTree.StoreCfg program := StackComposition.mapCfg Sum.inr none
      (printedOutput (exactParsedMargins as) s o)

theorem prefix_correct (as : List Symbol) (s : Data) (N : ℕ) :
    ∃ p,Executes program.code program.coin (output as s)
      (OnlineTree.initial program (TreeTyped.encode as) s) p ∧
      ∀ g : Option MatrixCode → ℚ,
        p.mean g=(ExactCoreProgram.prefixExperiment (exactParsedMargins as) N).mean g := by
  obtain ⟨p,hp,hpm⟩ := printed_correct (exactParsedMargins as) s N
  have hp' := hp.relabel program.code program.coin Sum.inr none (fun _ => rfl) (fun _ => rfl)
  obtain ⟨n,_,hn⟩ := exactParsedMarginsRealizer.correct as s
  obtain ⟨u,hu,hum,_⟩ := Executes.of_run exactParsedMarginsRealizer.program.code n
    (OnlineTree.initial (OnlineProc.deterministic exactParsedMarginsRealizer.program)
      (TreeTyped.encode as) s) none (encodeEnv (env (TreeTyped.encode (exactParsedMargins as)) .nil s)) hn
  have hu' := hu.relabel program.code program.coin Sum.inl
    (some (Sum.inr default)) (fun _ => rfl) (fun _ => rfl)
  refine ⟨u.bind (fun _ => p),hu'.bind _ _ (fun _ => hp'),?_⟩
  intro g
  rw [Experiment.mean_bind,hum]
  exact hpm g

end ContingencyTables.ExactTypedProgram

end OAI
