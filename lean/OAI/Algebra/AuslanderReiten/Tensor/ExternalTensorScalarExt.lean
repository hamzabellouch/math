import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorScalar
import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
import Mathlib.Algebra.Category.ModuleCat.Algebra

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.ExternalTensor
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable (M N : Type u) [AddCommGroup M] [AddCommGroup N]
variable [Module A M] [Module B N] [Module k M] [Module k N]
variable [IsScalarTower k A M] [IsScalarTower k B N]

def selfExtScalarEquiv (n : ℕ) :
    Ext (moduleObject k A B M N) (moduleObject k A B M N) n ≃ₗ[k]
      Ext (canonicalTensorObject k A B M N) (canonicalTensorObject k A B M N) n := by
  rw [canonicalTensorObject_eq]

end ArExplicit.ExternalTensor

end

end OAI
