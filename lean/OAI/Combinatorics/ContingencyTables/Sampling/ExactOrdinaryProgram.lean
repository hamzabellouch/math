import OAI.Combinatorics.ContingencyTables.Sampling.ExactBranchChoice
import OAI.Combinatorics.ContingencyTables.Sampling.AllSamplingAccuracy

namespace OAI

/-! # The finite ordinary branch of the exact sampler -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped MatchingFPRAS.PhysicalStream DensePrograms Polynomial

def exactOrdinaryWord (z : CompletionMargins×List Bool) : MatrixCode :=
  samplingMatrixAll (exactSamplingParameters z.1,z.2)

def exactOrdinaryWordRealizer : Realizer exactOrdinaryWord :=
  composition (f := fun z : CompletionMargins×List Bool => (exactSamplingParameters z.1,z.2))
    (g := samplingMatrixAll)
    (pair (composition (f := Prod.fst) (g := exactSamplingParameters)
      first exactSamplingParametersRealizer) second) samplingMatrixAllRealizer

lemma polynomial_exactOrdinaryWord : PolynomialTime exactOrdinaryWordRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_exactSamplingParameters) polynomial_second)
    polynomial_samplingMatrixAll

def exactOrdinary (z : CompletionMargins) : Experiment MatrixCode :=
  FiniteWordExecution.experiment exactOrdinaryBits exactOrdinaryWord z

noncomputable def exactOrdinaryRealizer : OnlineTree.Realizer exactOrdinary :=
  FiniteWordExecution.realizer exactOrdinaryBitsRealizer exactOrdinaryWordRealizer

lemma work_exactOrdinary : OnlineTree.WorkBound exactOrdinaryRealizer
    (FiniteWordExecution.wordMeasure exactOrdinaryBits) :=
  FiniteWordExecution.work_realizer polynomial_exactOrdinaryBits polynomial_exactOrdinaryWord

/-- The gate retains the margins for either branch. -/
def exactGate (z : CompletionMargins) : Experiment (Bool×CompletionMargins) :=
  (rareBranch z).map (fun rare => (rare,z))

noncomputable def exactGateRealizer : OnlineTree.Realizer exactGate :=
  (OnlineTree.pair rareBranchRealizer (OnlineTree.deterministic identity)).congr
    (by intro z g; simp only [Experiment.mean_bind,Experiment.mean,Experiment.mean_map,exactGate,id_eq])

lemma work_exactGate : OnlineTree.WorkBound exactGateRealizer exactParameterMeasure := by
  unfold exactGateRealizer
  apply OnlineTree.work_congr
  apply OnlineTree.work_pair work_rareBranch
    (OnlineTree.work_of_polynomial (OnlineTree.polynomial_deterministic polynomial_identity) X
      (by intro z; simp only [eval_X,exactParameterMeasure]; omega)) X
  intro z
  simp only [eval_X,exactParameterMeasure]
  omega

end ContingencyTables.ProfilePrograms

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms MatchingFPRAS.PhysicalStream
open scoped BigOperators

variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)

lemma exactOrdinaryWord_code (htotal : (∑ i,r i)=∑ j,c j)
    (bits : Fin (finiteSamplerBits r c (2*correctionPrecision r c)) → Bool) :
    exactOrdinaryWord ((List.ofFn r,List.ofFn c),List.ofFn bits)=
      matrixCode (scheduledTableDraw r c htotal (2*correctionPrecision r c) bits).val := by
  rw [exactOrdinaryWord,exactSamplingParameters_ofFn,samplingMatrixAll_code r c htotal]

end ContingencyTables.SmallGraphProfiles

end OAI
