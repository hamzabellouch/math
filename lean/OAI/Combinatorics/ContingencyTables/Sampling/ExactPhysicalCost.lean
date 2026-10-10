import OAI.Combinatorics.ContingencyTables.Sampling.ExactPhysicalProgram
import OAI.Combinatorics.ContingencyTables.Sampling.ExactTypedCost

namespace OAI

/-! # A physical cost bound for every finite prefix of the exact sampler -/

namespace ContingencyTables.ExactPhysicalCost
open MatchingFPRAS MatchingFPRAS.PhysicalStream MatchingFPRAS.PhysicalPost
open MatchingFPRAS.TreeTyped MatchingFPRAS.TreePost Turing
open DensePrograms ProfilePrograms ExactPhysicalProgram

attribute [local irreducible] ExactTypedProgram.program

noncomputable def typedBudget (as : List Symbol) (N B : ℕ) : ℕ :=
  exactParsedMarginsRealizer.cost as+ExactCoreCost.budget (exactParsedMargins as) N+B

noncomputable def budget (as : List Symbol) (N B : ℕ) : ℕ :=
  typedBudget as N B*OnlineStack.Executes.factor ExactTypedProgram.program.code
    (weight as) (typedBudget as N B)

/-- The compiler's quadratic overhead is charged to the actual finite
prefix cost. The executable program is still the same unbounded sampler. -/
theorem prefix_correct_cost (as : List Symbol) (N B : ℕ)
    (hB : (ExactCoreProgram.prefixExperiment (exactParsedMargins as) N).All
      (fun o => o.elim 0 GreedyFeasibleTable.printMatrixRealizer.cost≤B)) :
    ∃ q,Implements program.table (output as)
      (program.initial (Tape.mk₁ (packed as))) q ∧
      (∀ g : Option MatrixCode → ℚ,
        q.mean g=(ExactCoreProgram.prefixExperiment (exactParsedMargins as) N).mean g) ∧
      q.cost≤budget as N B := by
  obtain ⟨p,hp,hpm,hpc⟩ := ExactTypedCost.prefix_correct_cost as .nil N B hB
  obtain ⟨q,hq,hqm,hqc⟩ := hp.compile (weight as) (inputStacks_bound as)
  have hu := hq.up
  have hi := OnlineTree.cfg_packed ExactTypedProgram.program as (some default)
  change upCfg (OnlineStack.cfg (OnlineTree.initial ExactTypedProgram.program (encode as) .nil))=
    program.initial (Tape.mk₁ (packed as)) at hi
  rw [hi] at hu
  refine ⟨q,hu,(fun g => (hqm g).trans (hpm g)),?_⟩
  exact hqc.trans (Nat.mul_le_mul hpc (OnlineStack.Executes.factor_mono
    (weight as) (weight as) p.cost (typedBudget as N B) le_rfl hpc))

lemma typedBudget_le_scaled (as : List Symbol) (N B : ℕ) :
    typedBudget as N B≤typedBudget as 1 B*(N+1) := by
  have hc := Nat.mul_le_mul_left (typedBudget as 0 B) (show 1≤N+1 by omega)
  unfold typedBudget ExactCoreCost.budget at hc ⊢
  simp only [Nat.one_mul,Nat.zero_mul] at hc ⊢
  nlinarith

lemma factor_le_scaled (H K V : ℕ) (hV : 1≤V) :
    OnlineStack.Executes.factor ExactTypedProgram.program.code H (K*V)≤
      OnlineStack.Executes.factor ExactTypedProgram.program.code H K*V := by
  let A := OnlineStack.accesses ExactTypedProgram.program.code
  let O := OnlineStack.overhead ExactTypedProgram.program.code
  have hH : H+1≤(H+1)*V := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (H+1) hV
  have hinner : H+K*V*A+1≤(H+K*A+1)*V := by nlinarith
  have hA := Nat.mul_le_mul_left (2*A) hinner
  have hO : 1+2*A*(H+K*V*A+1)≤(1+2*A*(H+K*A+1))*V := by nlinarith
  have hfinal := Nat.mul_le_mul_left O hO
  change O*(1+2*A*(H+K*V*A+1))+1≤(O*(1+2*A*(H+K*A+1))+1)*V
  nlinarith

/-- One fixed coefficient bounds the compiler overhead for all prefix lengths. -/
lemma quadratic_budget (as : List Symbol) (N B : ℕ) :
    budget as N B≤budget as 1 B*(N+1)^2 := by
  have ht := typedBudget_le_scaled as N B
  have hf := OnlineStack.Executes.factor_mono (M := ExactTypedProgram.program.code)
    (weight as) (weight as) (typedBudget as N B) (typedBudget as 1 B*(N+1)) le_rfl ht
  have hs := factor_le_scaled (weight as) (typedBudget as 1 B) (N+1) (by omega)
  calc
    budget as N B≤(typedBudget as 1 B*(N+1))*
        (OnlineStack.Executes.factor ExactTypedProgram.program.code (weight as)
          (typedBudget as 1 B)*(N+1)) := Nat.mul_le_mul ht (hf.trans hs)
    _ = budget as 1 B*(N+1)^2 := by unfold budget; ring

end ContingencyTables.ExactPhysicalCost

end OAI
