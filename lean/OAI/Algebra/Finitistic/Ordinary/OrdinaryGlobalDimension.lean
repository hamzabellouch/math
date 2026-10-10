import OAI.Algebra.Finitistic.Ordinary.OrdinaryProductOpposite
import OAI.Algebra.Finitistic.Ordinary.OrdinaryTensorGlobalDimension

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation
universe u v
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]

/-- The manuscript's exact bound for D, on both sides and for arbitrary modules. -/
theorem ordinary_globalDimension_bound (DB : DirectedBound.DirectedSystem k B 3) (l : ℕ) :
    (⨆ M : ModuleCat.{max u v} (AlgebraD k l B), projectiveDimension M) ≤ (3*l+2 : ℕ) ∧
    (⨆ M : ModuleCat.{max u v} (AlgebraD k l B)ᵐᵒᵖ, projectiveDimension M) ≤ (3*l+2 : ℕ) := by
  have hB := DirectedBound.DirectedSystem.both_sides_projectiveDimension_le.{u,v} DB
  have hBC := tensor_projectiveDimension_bound.{u,v} DB l
  have hL (M : ModuleCat.{max u v} B) : projectiveDimension M ≤ (3*l+2 : ℕ) := by
    apply (hB.1 M).trans
    exact_mod_cast (show 3-1 ≤ 3*l+2 by omega)
  have hR (M : ModuleCat.{max u v} Bᵐᵒᵖ) : projectiveDimension M ≤ (3*l+2 : ℕ) := by
    apply (hB.2 M).trans
    exact_mod_cast (show 3-1 ≤ 3*l+2 by omega)
  exact ⟨iSup_le (fun M => ProductModules.product_module_bound B (B ⊗[k] ChainAlgebra k l)
      (3*l+2) hL hBC.1 M),
    iSup_le (fun M => ProductModules.opposite_product_module_bound B (B ⊗[k] ChainAlgebra k l)
      (3*l+2) hR hBC.2 M)⟩

variable {V W U : Type u} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  [AddCommGroup U] [Module k U]

/-- The bound for the actual three-vertex coefficient algebra and the actual Section 5 product D. -/
theorem source_ordinary_globalDimension_bound (μ : W →ₗ[k] V →ₗ[k] U) (l : ℕ) :
    (⨆ M : ModuleCat.{max u v} (AlgebraD k l (ThreeVertexAlgebra μ)), projectiveDimension M) ≤ (3*l+2 : ℕ) ∧
    (⨆ M : ModuleCat.{max u v} (AlgebraD k l (ThreeVertexAlgebra μ))ᵐᵒᵖ, projectiveDimension M) ≤ (3*l+2 : ℕ) :=
  ordinary_globalDimension_bound (ThreeVertexAlgebra.directedSystem μ) l
end LittleFinitistic.OrdinarySimulation

end

end OAI
