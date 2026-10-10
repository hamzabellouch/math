import OAI.Combinatorics.ContingencyTables.Sampling.ExactSamplingParameters
import OAI.Combinatorics.ContingencyTables.Machines.ListWordProgram

namespace OAI

/-! # The exact dyadic gate that selects the rare correction branch -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped MatchingFPRAS.PhysicalStream DensePrograms Polynomial

/-- All zero bits select correction; every other word selects the ordinary draw. -/
def rareWord (z : CompletionMargins×List Bool) : Bool := decide (StackAddition.value z.2=0)

def rareWordRealizer : Realizer rareWord :=
  composition (f := fun z : CompletionMargins×List Bool => (StackAddition.value z.2,0))
    (g := fun p : ℕ×ℕ => decide (p.1=p.2))
    (pair (composition second bitValue) (constant 0)) natEqual

lemma polynomial_rareWord : PolynomialTime rareWordRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition polynomial_second polynomial_bitValue)
    (polynomial_constant 0)) polynomial_natEqual

def rareBranch (z : CompletionMargins) : Experiment Bool :=
  FiniteWordExecution.experiment exactPrecision rareWord z

noncomputable def rareBranchRealizer : OnlineTree.Realizer rareBranch :=
  FiniteWordExecution.realizer exactPrecisionRealizer rareWordRealizer

lemma work_rareBranch : OnlineTree.WorkBound rareBranchRealizer exactParameterMeasure := by
  apply OnlineTree.work_remeasure
    (FiniteWordExecution.work_realizer polynomial_exactPrecision polynomial_rareWord) X
  intro z
  simp only [FiniteWordExecution.wordMeasure,exactParameterMeasure,eval_X]
  omega

lemma rareBranch_probability (z : CompletionMargins) :
    (rareBranch z).mean (fun rare => if rare then 1 else 0)=1/(2:ℚ)^(exactPrecision z) := by
  rw [rareBranch,FiniteWordExecution.experiment_mean]
  simp only [rareWord,decide_eq_true_eq,bitValue_eq_word]
  let zeroWord : Fin (exactPrecision z) → Bool :=
    (FairBits.binaryWordEquiv (exactPrecision z)).symm ⟨0,by positivity⟩
  have he (bits : Fin (exactPrecision z) → Bool) :
      (FairBits.binaryWordEquiv (exactPrecision z) bits).val=0 ↔ bits=zeroWord := by
    constructor
    · intro h
      apply (FairBits.binaryWordEquiv (exactPrecision z)).injective
      apply Fin.ext
      simpa only [zeroWord,Equiv.apply_symm_apply] using h
    · intro h
      rw [h]
      simp only [zeroWord,Equiv.apply_symm_apply]
  simp only [he,average,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

end ContingencyTables.ProfilePrograms

end OAI
