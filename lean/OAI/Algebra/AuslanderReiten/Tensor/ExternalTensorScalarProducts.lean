import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorScalarExt

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.ExternalTensor
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable (M N : Type u) [AddCommGroup M] [AddCommGroup N]
variable [Module A M] [Module B N] [mM : Module k M] [mN : Module k N]
variable [IsScalarTower k A M] [IsScalarTower k B N]

@[simp] theorem selfExtScalarEquiv_identity :
    selfExtScalarEquiv k A B M N 0 (Ext.mk₀ (𝟙 (moduleObject k A B M N))) =
      Ext.mk₀ (𝟙 (canonicalTensorObject k A B M N)) := by
  cases canonicalScalar_eq k A M (mM := mM)
  cases canonicalScalar_eq k B N (mM := mN)
  rfl

theorem selfExtScalarEquiv_comp {i j n : ℕ}
    (x : Ext (moduleObject k A B M N) (moduleObject k A B M N) i)
    (y : Ext (moduleObject k A B M N) (moduleObject k A B M N) j) (h : i+j=n) :
    selfExtScalarEquiv k A B M N n (x.comp y h) =
      (selfExtScalarEquiv k A B M N i x).comp (selfExtScalarEquiv k A B M N j y) h := by
  cases canonicalScalar_eq k A M (mM := mM)
  cases canonicalScalar_eq k B N (mM := mN)
  rfl

theorem selfExtScalarEquiv_symm_comp {i j n : ℕ}
    (x : Ext (canonicalTensorObject k A B M N) (canonicalTensorObject k A B M N) i)
    (y : Ext (canonicalTensorObject k A B M N) (canonicalTensorObject k A B M N) j) (h : i+j=n) :
    (selfExtScalarEquiv k A B M N n).symm (x.comp y h) =
      ((selfExtScalarEquiv k A B M N i).symm x).comp ((selfExtScalarEquiv k A B M N j).symm y) h := by
  apply (selfExtScalarEquiv k A B M N n).injective
  rw [selfExtScalarEquiv_comp]
  simp

end ArExplicit.ExternalTensor

end

end OAI
