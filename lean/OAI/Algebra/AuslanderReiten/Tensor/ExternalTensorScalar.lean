import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorModule
import OAI.Algebra.AuslanderReiten.BaseChange.ScalarExtensionComplete

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace ArExplicit.ExternalTensor
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable (M N : Type u) [AddCommGroup M] [AddCommGroup N]
variable [Module A M] [Module B N] [mM : Module k M] [mN : Module k N]
variable [IsScalarTower k A M] [IsScalarTower k B N]

theorem canonicalScalar_eq :
    moduleCatBaseModule (k := k) (R := A) (ModuleCat.of A M) = mM := by
  apply Module.ext'
  intro a x
  exact IsScalarTower.algebraMap_smul A a x

def canonicalTensorObject : ModuleCat.{u} (A ⊗[k] B) :=
  letI : Module k M := moduleCatBaseModule (k := k) (R := A) (ModuleCat.of A M)
  letI : Module k N := moduleCatBaseModule (k := k) (R := B) (ModuleCat.of B N)
  letI : IsScalarTower k A M := moduleCatBaseTower (k := k) (R := A) (ModuleCat.of A M)
  letI : IsScalarTower k B N := moduleCatBaseTower (k := k) (R := B) (ModuleCat.of B N)
  moduleObject k A B M N

theorem canonicalTensorObject_eq :
    canonicalTensorObject k A B M N = moduleObject k A B M N := by
  cases canonicalScalar_eq k A M (mM := mM)
  cases canonicalScalar_eq k B N (mM := mN)
  rfl

def canonicalTensorIso : canonicalTensorObject k A B M N ≅ moduleObject k A B M N :=
  eqToIso (canonicalTensorObject_eq k A B M N)

end ArExplicit.ExternalTensor

end

end OAI
