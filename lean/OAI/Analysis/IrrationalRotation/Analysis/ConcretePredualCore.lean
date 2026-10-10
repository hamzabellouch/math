import OAI.Analysis.IrrationalRotation.Model.VectorTraceState
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Topology.Algebra.Module.Basic

namespace OAI

noncomputable section
namespace Invariant233.ConcretePredual

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def vectorFunctional (M : VonNeumannAlgebra H) (x y : H) : StrongDual ℂ M :=
  ((innerSL ℂ x).comp ((ContinuousLinearMap.apply ℂ H) y)).comp
    M.toSubalgebra.toSubmodule.subtypeL

@[simp] theorem vectorFunctional_apply (M : VonNeumannAlgebra H) (x y : H) (A : M) :
    vectorFunctional M x y A = inner ℂ x ((A : H →L[ℂ] H) y) := rfl

def predual (M : VonNeumannAlgebra H) : Submodule ℂ (StrongDual ℂ M) :=
  (Submodule.span ℂ (Set.range (fun xy : H × H => vectorFunctional M xy.1 xy.2))).topologicalClosure

theorem vectorFunctional_mem (M : VonNeumannAlgebra H) (x y : H) :
    vectorFunctional M x y ∈ predual M :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨(x, y), rfl⟩)

def vector (M : VonNeumannAlgebra H) (x y : H) : predual M :=
  ⟨vectorFunctional M x y, vectorFunctional_mem M x y⟩

@[simp] theorem vector_coe (M : VonNeumannAlgebra H) (x y : H) :
    (vector M x y : StrongDual ℂ M) = vectorFunctional M x y := rfl

def evaluation (M : VonNeumannAlgebra H) (A : M) : StrongDual ℂ (predual M) :=
  ((ContinuousLinearMap.apply ℂ ℂ) A).comp (predual M).subtypeL

@[simp] theorem evaluation_apply (M : VonNeumannAlgebra H) (A : M) (f : predual M) :
    evaluation M A f = (f : StrongDual ℂ M) A := rfl

@[simp] theorem evaluation_vector (M : VonNeumannAlgebra H) (A : M) (x y : H) :
    evaluation M A (vector M x y) = inner ℂ x ((A : H →L[ℂ] H) y) := rfl

end Invariant233.ConcretePredual

end

end OAI
