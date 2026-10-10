import OAI.Algebra.AuslanderReiten.BaseChange.ScalarExtension
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Flat.Basic

namespace OAI

noncomputable section
open scoped TensorProduct

namespace ArExplicit

universe u v w

variable (k : Type u) [Field k] (E : Type v) [Field E] [Algebra k E]
  (R : Type w) [Ring R] [Algebra k R]
  {M N L : Type w}
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
  [AddCommGroup N] [Module R N] [Module k N] [IsScalarTower k R N]
  [AddCommGroup L] [Module R L] [Module k L] [IsScalarTower k R L]

attribute [local instance] scalarExtensionModule

theorem scalarExtensionMap_exact (f : M →ₗ[R] N) (g : N →ₗ[R] L)
    (h : Function.Exact f g) :
    Function.Exact (scalarExtensionMap k E R f) (scalarExtensionMap k E R g) := by
  change Function.Exact ((f.restrictScalars k).lTensor E) ((g.restrictScalars k).lTensor E)
  exact Module.Flat.lTensor_exact E h

theorem scalarExtensionMap_injective (f : M →ₗ[R] N) (h : Function.Injective f) :
    Function.Injective (scalarExtensionMap k E R f) := by
  change Function.Injective ((f.restrictScalars k).lTensor E)
  exact Module.Flat.lTensor_preserves_injective_linearMap (f.restrictScalars k) h

theorem scalarExtensionMap_surjective (f : M →ₗ[R] N) (h : Function.Surjective f) :
    Function.Surjective (scalarExtensionMap k E R f) := by
  change Function.Surjective ((f.restrictScalars k).lTensor E)
  exact LinearMap.lTensor_surjective E h

end ArExplicit

end

end OAI
