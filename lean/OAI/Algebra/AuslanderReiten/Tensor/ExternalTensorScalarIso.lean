import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorScalarExt
import OAI.Algebra.AuslanderReiten.Ext.ExtIsoFunctor

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

theorem selfExtScalarEquiv_eq_iso (n : ℕ)
    (x : Ext (moduleObject k A B M N) (moduleObject k A B M N) n) :
    selfExtScalarEquiv k A B M N n x =
      selfExtIso (k := k) (canonicalTensorIso k A B M N).symm n x := by
  cases canonicalScalar_eq k A M (mM := mM)
  cases canonicalScalar_eq k B N (mM := mN)
  change x = ((Ext.mk₀ (𝟙 _)).comp x (zero_add n)).comp (Ext.mk₀ (𝟙 _)) (add_zero n)
  simp

theorem selfExtScalarEquiv_symm_eq_iso (n : ℕ)
    (x : Ext (canonicalTensorObject k A B M N) (canonicalTensorObject k A B M N) n) :
    (selfExtScalarEquiv k A B M N n).symm x =
      selfExtIso (k := k) (canonicalTensorIso k A B M N) n x := by
  apply (selfExtScalarEquiv k A B M N n).injective
  rw [LinearEquiv.apply_symm_apply, selfExtScalarEquiv_eq_iso]
  simp [selfExtIso_apply]

end ArExplicit.ExternalTensor

end

end OAI
