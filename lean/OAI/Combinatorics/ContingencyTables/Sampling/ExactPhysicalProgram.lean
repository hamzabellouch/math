import OAI.Combinatorics.ContingencyTables.Sampling.ExactTypedProgram
import OAI.Combinatorics.ContingencyTables.Sampling.PhysicalPartialSequence

namespace OAI

/-! # Physical execution of the parsed and printed exact sampler -/

namespace ContingencyTables.ExactPhysicalProgram
open MatchingFPRAS MatchingFPRAS.PhysicalStream MatchingFPRAS.PhysicalPost
open MatchingFPRAS.TreeTyped MatchingFPRAS.TreePost Turing
open DensePrograms

noncomputable def ofOnline (P : OnlineProc.Proc (TreeMachine.K TreeFunction.Reg)) : Program where
  State := OnlineStack.Q (TreeMachine.K TreeFunction.Reg) (fun _ => Bool)
    P.Label RegisterProc.Store
  table := liftBool (OnlineStack.table P.code P.coin)
  states := OnlineStack.states P.code
  supported := liftBool_supported _ _
    (OnlineStack.table_supported P.code P.coin)
  entry := OnlineStack.initialState
  entry_mem := OnlineStack.initialState_mem P.code

noncomputable def program : Program := ofOnline ExactTypedProgram.program

attribute [local irreducible] ExactTypedProgram.program

noncomputable def output (as : List Symbol) (o : Option MatrixCode) : Cfg Symbol program.State :=
  upCfg (OnlineStack.cfg (ExactTypedProgram.output as .nil o))

lemma output_some (as : List Symbol) (X : MatrixCode) :
    output as (some X)=program.final (Tape.mk₁ (packed (GreedyFeasibleTable.printMatrix X))) := by
  change upCfg (OnlineStack.cfg
    (⟨none,none,inputStacks (GreedyFeasibleTable.printMatrix X)⟩ :
      OnlineTree.StoreCfg ExactTypedProgram.program))=_
  exact OnlineTree.cfg_packed ExactTypedProgram.program (GreedyFeasibleTable.printMatrix X) none

lemma output_none_live (as : List Symbol) : (output as none).state≠none := by
  change (some _ : Option program.State)≠none
  exact Option.some_ne_none _

/-- Every finite exact-sampling prefix runs on one fixed finite physical
transition table, including its live failure endpoint. -/
theorem prefix_correct (as : List Symbol) (N : ℕ) :
    ∃ q,Implements program.table (output as)
      (program.initial (Tape.mk₁ (packed as))) q ∧
      ∀ g : Option MatrixCode → ℚ,
        q.mean g=(ExactCoreProgram.prefixExperiment (ProfilePrograms.exactParsedMargins as) N).mean g := by
  obtain ⟨p,hp,hpm⟩ := ExactTypedProgram.prefix_correct as .nil N
  obtain ⟨q,hq,hqm,_⟩ := hp.compile (weight as) (inputStacks_bound as)
  have hu := hq.up
  have hi := OnlineTree.cfg_packed ExactTypedProgram.program as (some default)
  change upCfg (OnlineStack.cfg (OnlineTree.initial ExactTypedProgram.program (encode as) .nil))=
    program.initial (Tape.mk₁ (packed as)) at hi
  rw [hi] at hu
  exact ⟨q,hu,fun g => (hqm g).trans (hpm g)⟩

end ContingencyTables.ExactPhysicalProgram

end OAI
