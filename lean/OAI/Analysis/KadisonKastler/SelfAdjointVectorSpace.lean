import OAI.Analysis.KadisonKastler.Algebra
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

namespace OAI

/-! # The closed real space of self-adjoint algebra vectors -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance selfAdjointSpaceReal : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H

def selfAdjointVectorMap (M : VonNeumannAlgebra H) (Ω : H) :
    selfAdjoint (Algebra M) →ₗ[ℝ] H where
  toFun a := a.val.val Ω
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def selfAdjointVectorSpace (M : VonNeumannAlgebra H) (Ω : H) : Submodule ℝ H :=
  (selfAdjointVectorMap M Ω).range.topologicalClosure

instance selfAdjointVectorSpace_complete (M : VonNeumannAlgebra H) (Ω : H) :
    CompleteSpace (selfAdjointVectorSpace M Ω) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

def selfAdjointVectorInSpace (M : VonNeumannAlgebra H) (Ω : H)
    (a : selfAdjoint (Algebra M)) : selfAdjointVectorSpace M Ω :=
  ⟨selfAdjointVectorMap M Ω a, Submodule.le_topologicalClosure _ ⟨a, rfl⟩⟩

theorem selfAdjointVectorInSpace_dense (M : VonNeumannAlgebra H) (Ω : H) :
    DenseRange (selfAdjointVectorInSpace M Ω) := by
  apply Metric.denseRange_iff.mpr
  intro x ε hε
  have hx := x.property
  change x.val ∈ closure (Set.range (selfAdjointVectorMap M Ω)) at hx
  obtain ⟨v, ⟨a, rfl⟩, ha⟩ := Metric.mem_closure_iff.mp hx ε hε
  exact ⟨a, ha⟩

theorem inner_selfAdjointVector_projection (M : VonNeumannAlgebra H) (Ω : H)
    (a : selfAdjoint (Algebra M)) (v : H) :
    inner ℝ (selfAdjointVectorMap M Ω a) ((selfAdjointVectorSpace M Ω).starProjection v) =
      inner ℝ (selfAdjointVectorMap M Ω a) v := by
  exact Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left
    (selfAdjointVectorInSpace M Ω a) v

end

end KadisonKastler

end OAI
