import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

namespace OAI

namespace Invariant233.Fields

noncomputable def rationalComplex (q : ℚ × ℚ) : ℂ :=
  Complex.equivRealProdCLM.symm ((q.1 : ℝ), (q.2 : ℝ))

variable {ι H F : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

noncomputable def columnOperator (b : HilbertBasis ι ℂ H) (c : ι → F) : H →L[ℂ] F :=
  (Finsupp.linearCombination ℂ c).extendOfNorm (Finsupp.linearCombination ℂ b)

end Invariant233.Fields

end OAI
