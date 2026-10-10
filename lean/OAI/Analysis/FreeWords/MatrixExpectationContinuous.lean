import Mathlib
import OAI.Analysis.FreeWords.AmplifiedModelDefinitions

namespace OAI

noncomputable section

namespace KKMatrixExpectation

open KKTraceTransfer KKFreeLiftFrontier

noncomputable section

open scoped Matrix.Norms.Operator ComplexOrder

variable {H:Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance concreteOrder (M:VonNeumannAlgebra H) : PartialOrder (ConcreteAlgebra M) :=
  CStarAlgebra.spectralOrder _

local instance concreteLE (M:VonNeumannAlgebra H) : LE (ConcreteAlgebra M) := (concreteOrder M).toLE

local instance concretePreorder (M:VonNeumannAlgebra H) : Preorder (ConcreteAlgebra M) := (concreteOrder M).toPreorder

local instance concreteSOR (M:VonNeumannAlgebra H) : StarOrderedRing (ConcreteAlgebra M) :=
  CStarAlgebra.spectralOrderedRing _

def matrixExpectationCLM {M:VonNeumannAlgebra H} (τ:FaithfulNormalTrace M) (n:ℕ) :
    MatrixAlgebra n M →L[ℂ] MatrixAlgebra n M :=
  { matrixExpectation τ.map n with
    cont := by
      apply continuous_pi
      intro i
      apply continuous_pi
      intro j
      exact (continuous_algebraMap ℂ (ConcreteAlgebra M)).comp
        ((map_continuous (tracePositive τ)).comp (by fun_prop)) }

@[simp] theorem matrixExpectationCLM_apply {M:VonNeumannAlgebra H} (τ:FaithfulNormalTrace M) (n:ℕ)
    (x:MatrixAlgebra n M) : matrixExpectationCLM τ n x=matrixExpectation τ.map n x := rfl

theorem matrixExpectation_idem {M:VonNeumannAlgebra H} (τ:FaithfulNormalTrace M) (n:ℕ)
    (x:MatrixAlgebra n M) : matrixExpectationCLM τ n (matrixExpectationCLM τ n x)=matrixExpectationCLM τ n x :=
  matrixExpectation_fix τ.map τ.normalized n _ (matrixExpectation_range τ.map n x)

theorem matrixExpectationCLM_right {M:VonNeumannAlgebra H} (τ:FaithfulNormalTrace M) (n:ℕ)
    (a b:MatrixAlgebra n M) : matrixExpectationCLM τ n (a*matrixExpectationCLM τ n b)=
      matrixExpectationCLM τ n a*matrixExpectationCLM τ n b :=
  matrixExpectation_right τ.map n a _ (matrixExpectation_range τ.map n b)

theorem matrixExpectation_zero_iff {M:VonNeumannAlgebra H} (τ:FaithfulNormalTrace M) (n:ℕ)
    (x:MatrixAlgebra n M) : matrixExpectation τ.map n x=0 ↔ ∀i j,τ.map (x i j)=0 := by
  constructor
  · intro hx i j
    have h := congrArg (fun X:MatrixAlgebra n M => τ.map (X i j)) hx
    simpa only [matrixExpectation_apply,trace_algebraMap τ.map τ.normalized,Matrix.zero_apply,map_zero] using h
  · intro h
    ext i j
    simp only [matrixExpectation_apply,h,map_zero,Matrix.zero_apply]

theorem trace_center_entry {M:VonNeumannAlgebra H} (τ:FaithfulNormalTrace M) (n:ℕ)
    (x:MatrixAlgebra n M) (i j:Fin n) : τ.map ((x-matrixExpectation τ.map n x) i j)=0 := by
  simp only [Matrix.sub_apply,map_sub,matrixExpectation_apply,trace_algebraMap τ.map τ.normalized,sub_self]

end

end KKMatrixExpectation
end

end OAI
