import OAI.Algebra.Finitistic.Ordinary.OrdinaryTensorDirected
import OAI.Algebra.Finitistic.Encoding.ThreeVertexAlgebra

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation
universe u v
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]

/-- The source tensor algebra bound uses exactly 3(l+1) directed vertices, on both sides. -/
theorem tensor_globalDimension_bound (DB : DirectedBound.DirectedSystem k B 3) (l : ℕ) :
    (⨆ M : ModuleCat.{max u v} (B ⊗[k] ChainAlgebra k l), projectiveDimension M) ≤ (3*l+2 : ℕ) ∧
    (⨆ M : ModuleCat.{max u v} (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ, projectiveDimension M) ≤ (3*l+2 : ℕ) := by
  have h := DirectedBound.DirectedSystem.both_sides_globalDimension_le.{u,v}
    (TensorDirected.directedSystem DB (ChainAlgebra.directedSystem k l))
  have hn : (l+1)*3-1 = 3*l+2 := by omega
  simpa only [hn] using h

/-- The corresponding bound holds for each arbitrary left or right module. -/
theorem tensor_projectiveDimension_bound (DB : DirectedBound.DirectedSystem k B 3) (l : ℕ) :
    (∀ M : ModuleCat.{max u v} (B ⊗[k] ChainAlgebra k l), projectiveDimension M ≤ (3*l+2 : ℕ)) ∧
    (∀ M : ModuleCat.{max u v} (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ, projectiveDimension M ≤ (3*l+2 : ℕ)) := by
  have h := DirectedBound.DirectedSystem.both_sides_projectiveDimension_le.{u,v}
    (TensorDirected.directedSystem DB (ChainAlgebra.directedSystem k l))
  have hn : (l+1)*3-1 = 3*l+2 := by omega
  simpa only [hn] using h

variable {V W U : Type u} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  [AddCommGroup U] [Module k U]

/-- The bound for the actual three-vertex coefficient algebra used by the manuscript. -/
theorem source_tensor_globalDimension_bound (μ : W →ₗ[k] V →ₗ[k] U) (l : ℕ) :
    (⨆ M : ModuleCat.{max u v} (ThreeVertexAlgebra μ ⊗[k] ChainAlgebra k l), projectiveDimension M) ≤ (3*l+2 : ℕ) ∧
    (⨆ M : ModuleCat.{max u v} (ThreeVertexAlgebra μ ⊗[k] ChainAlgebra k l)ᵐᵒᵖ, projectiveDimension M) ≤ (3*l+2 : ℕ) :=
  tensor_globalDimension_bound (ThreeVertexAlgebra.directedSystem μ) l
end LittleFinitistic.OrdinarySimulation

end

end OAI
