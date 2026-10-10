import OAI.Combinatorics.ContingencyTables.Sampling.ExactPhysicalProgram
import OAI.Combinatorics.ContingencyTables.Sampling.ExactGateTyped

namespace OAI

/-! # The cheap exact-sampling prefix on the same physical program -/

namespace ContingencyTables.ExactGatePhysical
open MatchingFPRAS MatchingFPRAS.PhysicalStream MatchingFPRAS.PhysicalPost
open MatchingFPRAS.TreeTyped MatchingFPRAS.TreePost Turing
open DensePrograms ProfilePrograms

attribute [local irreducible] ExactTypedProgram.program

noncomputable def output (as : List Symbol) (o : Option MatrixCode) :
    Cfg Symbol ExactPhysicalProgram.program.State :=
  upCfg (OnlineStack.cfg (ExactGateTyped.output as .nil o))

lemma output_some (as : List Symbol) (X : MatrixCode) :
    output as (some X)=ExactPhysicalProgram.program.final
      (Tape.mk₁ (packed (GreedyFeasibleTable.printMatrix X))) := by
  change upCfg (OnlineStack.cfg
    (⟨none,none,inputStacks (GreedyFeasibleTable.printMatrix X)⟩ :
      OnlineTree.StoreCfg ExactTypedProgram.program))=_
  exact OnlineTree.cfg_packed ExactTypedProgram.program (GreedyFeasibleTable.printMatrix X) none

lemma output_none_live (as : List Symbol) : (output as none).state≠none := by
  change (some _ : Option ExactPhysicalProgram.program.State)≠none
  exact Option.some_ne_none _

noncomputable def typedBudget (as : List Symbol) (B : ℕ) : ℕ :=
  exactParsedMarginsRealizer.cost as+ExactGatePrefix.budget (exactParsedMargins as)+B

noncomputable def budget (as : List Symbol) (B : ℕ) : ℕ :=
  typedBudget as B*OnlineStack.Executes.factor ExactTypedProgram.program.code
    (weight as) (typedBudget as B)

theorem prefix_correct_cost (as : List Symbol) (B : ℕ)
    (hB : (ExactGatePrefix.experiment (exactParsedMargins as)).All
      (fun o => o.elim 0 GreedyFeasibleTable.printMatrixRealizer.cost≤B)) :
    ∃ q,Implements ExactPhysicalProgram.program.table (output as)
      (ExactPhysicalProgram.program.initial (Tape.mk₁ (packed as))) q ∧
      (∀ g : Option MatrixCode → ℚ,
        q.mean g=(ExactGatePrefix.experiment (exactParsedMargins as)).mean g) ∧
      q.cost≤budget as B := by
  obtain ⟨p,hp,hpm,hpc⟩ := ExactGateTyped.prefix_correct_cost as .nil B hB
  obtain ⟨q,hq,hqm,hqc⟩ := hp.compile (weight as) (inputStacks_bound as)
  have hu := hq.up
  have hi := OnlineTree.cfg_packed ExactTypedProgram.program as (some default)
  change upCfg (OnlineStack.cfg (OnlineTree.initial ExactTypedProgram.program (encode as) .nil))=
    ExactPhysicalProgram.program.initial (Tape.mk₁ (packed as)) at hi
  rw [hi] at hu
  refine ⟨q,hu,(fun g => (hqm g).trans (hpm g)),?_⟩
  exact hqc.trans (Nat.mul_le_mul hpc (OnlineStack.Executes.factor_mono
    (weight as) (weight as) p.cost (typedBudget as B) le_rfl hpc))

end ContingencyTables.ExactGatePhysical

end OAI
