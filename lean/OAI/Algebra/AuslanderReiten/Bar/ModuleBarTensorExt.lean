import OAI.Algebra.AuslanderReiten.Bar.ModuleBarNative
import OAI.Algebra.AuslanderReiten.Ext.ExtKunnethActions
import OAI.Algebra.AuslanderReiten.Ext.ExtKunnethIdentity
import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorScalar
import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorScalarProducts

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.ModuleBar
universe u
variable (k R S M N : Type u) [Field k] [CharP k 2]
  [Ring R] [Algebra k R] [Module.Finite k R] [Ring S] [Algebra k S] [Module.Finite k S]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M] [Module.Finite k M]
  [AddCommGroup N] [Module S N] [Module k N] [IsScalarTower k S N] [Module.Finite k N]

def nativeTensorKunneth (n : ℕ) :
    Ext (ExternalTensor.canonicalTensorObject k R S M N)
      (ExternalTensor.canonicalTensorObject k R S M N) n ≃ₗ[k]
        ExternalTensor.extCoefficients k R S (ModuleCat.of R M) (ModuleCat.of R M)
          (ModuleCat.of S N) (ModuleCat.of S N) n :=
  ExternalTensor.extKunnethEquiv k R S (nativeResolution k R M) (nativeResolution k S N)
    (ModuleCat.of R M) (ModuleCat.of S N) n

def tensorKunneth (n : ℕ) :
    Ext (ExternalTensor.moduleObject k R S M N) (ExternalTensor.moduleObject k R S M N) n ≃ₗ[k]
      ExternalTensor.extCoefficients k R S (ModuleCat.of R M) (ModuleCat.of R M)
        (ModuleCat.of S N) (ModuleCat.of S N) n :=
  (ExternalTensor.selfExtScalarEquiv k R S M N n).trans (nativeTensorKunneth k R S M N n)

variable [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} S)]
  [HasDerivedCategory (ModuleCat.{u} (R ⊗[k] S))]

theorem nativeTensorKunneth_identity :
    nativeTensorKunneth k R S M N 0 (Ext.mk₀ (𝟙 (ExternalTensor.canonicalTensorObject k R S M N))) =
      (Pi.single ⟨(0,0),rfl⟩ (Ext.mk₀ (𝟙 (ModuleCat.of R M)) ⊗ₜ[k]
        Ext.mk₀ (𝟙 (ModuleCat.of S N))) :
          ExternalTensor.extCoefficients k R S (ModuleCat.of R M) (ModuleCat.of R M)
            (ModuleCat.of S N) (ModuleCat.of S N) 0) :=
  ExternalTensor.extKunnethEquiv_identity k R S (nativeResolution k R M) (nativeResolution k S N)

theorem tensorKunneth_identity :
    tensorKunneth k R S M N 0 (Ext.mk₀ (𝟙 (ExternalTensor.moduleObject k R S M N))) =
      (Pi.single ⟨(0,0),rfl⟩ (Ext.mk₀ (𝟙 (ModuleCat.of R M)) ⊗ₜ[k]
        Ext.mk₀ (𝟙 (ModuleCat.of S N))) :
          ExternalTensor.extCoefficients k R S (ModuleCat.of R M) (ModuleCat.of R M)
            (ModuleCat.of S N) (ModuleCat.of S N) 0) := by
  unfold tensorKunneth
  rw [LinearEquiv.trans_apply, ExternalTensor.selfExtScalarEquiv_identity]
  exact nativeTensorKunneth_identity k R S M N

variable (p : AbsoluteBar.Cochain3 k R) (hp : AbsoluteBar.IsCocycle3 k R p)
variable (r : AbsoluteBar.Cochain3 k S) (hr : AbsoluteBar.IsCocycle3 k S r)

def nativeTensorFirst : Ext (ExternalTensor.canonicalTensorObject k R S M N)
    (ExternalTensor.canonicalTensorObject k R S M N) 3 :=
  ExternalTensor.firstCubicExt k R S (nativeResolution k R M) (nativeResolution k S N)
    (nativeCubicMap k R M p) (nativeCubicMap_comm k R M p hp)

def nativeTensorSecond : Ext (ExternalTensor.canonicalTensorObject k R S M N)
    (ExternalTensor.canonicalTensorObject k R S M N) 3 :=
  ExternalTensor.secondCubicExt k R S (nativeResolution k R M) (nativeResolution k S N)
    (nativeCubicMap k S N r) (nativeCubicMap_comm k S N r hr)

def tensorFirst : Ext (ExternalTensor.moduleObject k R S M N)
    (ExternalTensor.moduleObject k R S M N) 3 :=
  (ExternalTensor.selfExtScalarEquiv k R S M N 3).symm (nativeTensorFirst k R S M N p hp)

def tensorSecond : Ext (ExternalTensor.moduleObject k R S M N)
    (ExternalTensor.moduleObject k R S M N) 3 :=
  (ExternalTensor.selfExtScalarEquiv k R S M N 3).symm (nativeTensorSecond k R S M N r hr)

omit [HasDerivedCategory (ModuleCat S)] in
theorem nativeTensorFirst_action (n : ℕ)
    (x : Ext (ExternalTensor.canonicalTensorObject k R S M N)
      (ExternalTensor.canonicalTensorObject k R S M N) n) :
    nativeTensorKunneth k R S M N (n+3) ((nativeTensorFirst k R S M N p hp).comp x (by omega)) =
      ExternalTensor.coefficientFirst k R S (ModuleCat.of R M) (ModuleCat.of R M)
        (ModuleCat.of S N) (ModuleCat.of S N) (extClass3 k R M p hp) n
          (nativeTensorKunneth k R S M N n x) := by
  unfold nativeTensorKunneth nativeTensorFirst
  exact ExternalTensor.firstCubicExt_kunneth_of_class k R S
    (nativeResolution k R M) (nativeResolution k S N) (ModuleCat.of R M) (ModuleCat.of S N)
    (nativeCubicMap k R M p) (nativeCubicMap_comm k R M p hp) _
    (nativeCubicMap_class k R M p hp) n x

omit [HasDerivedCategory (ModuleCat R)] in
theorem nativeTensorSecond_action (n : ℕ)
    (x : Ext (ExternalTensor.canonicalTensorObject k R S M N)
      (ExternalTensor.canonicalTensorObject k R S M N) n) :
    nativeTensorKunneth k R S M N (n+3) ((nativeTensorSecond k R S M N r hr).comp x (by omega)) =
      ExternalTensor.coefficientSecond k R S (ModuleCat.of R M) (ModuleCat.of R M)
        (ModuleCat.of S N) (ModuleCat.of S N) (extClass3 k S N r hr) n
          (nativeTensorKunneth k R S M N n x) := by
  unfold nativeTensorKunneth nativeTensorSecond
  exact ExternalTensor.secondCubicExt_kunneth_of_class k R S
    (nativeResolution k R M) (nativeResolution k S N) (ModuleCat.of R M) (ModuleCat.of S N)
    (nativeCubicMap k S N r) (nativeCubicMap_comm k S N r hr) _
    (nativeCubicMap_class k S N r hr) n x

omit [HasDerivedCategory (ModuleCat S)] in
theorem tensorFirst_action (n : ℕ)
    (x : Ext (ExternalTensor.moduleObject k R S M N) (ExternalTensor.moduleObject k R S M N) n) :
    tensorKunneth k R S M N (n+3) ((tensorFirst k R S M N p hp).comp x (by omega)) =
      ExternalTensor.coefficientFirst k R S (ModuleCat.of R M) (ModuleCat.of R M)
        (ModuleCat.of S N) (ModuleCat.of S N) (extClass3 k R M p hp) n
          (tensorKunneth k R S M N n x) := by
  unfold tensorKunneth
  simp only [LinearEquiv.trans_apply, ExternalTensor.selfExtScalarEquiv_comp,
    tensorFirst, LinearEquiv.apply_symm_apply]
  exact nativeTensorFirst_action k R S M N p hp n _

omit [HasDerivedCategory (ModuleCat R)] in
theorem tensorSecond_action (n : ℕ)
    (x : Ext (ExternalTensor.moduleObject k R S M N) (ExternalTensor.moduleObject k R S M N) n) :
    tensorKunneth k R S M N (n+3) ((tensorSecond k R S M N r hr).comp x (by omega)) =
      ExternalTensor.coefficientSecond k R S (ModuleCat.of R M) (ModuleCat.of R M)
        (ModuleCat.of S N) (ModuleCat.of S N) (extClass3 k S N r hr) n
          (tensorKunneth k R S M N n x) := by
  unfold tensorKunneth
  simp only [LinearEquiv.trans_apply, ExternalTensor.selfExtScalarEquiv_comp,
    tensorSecond, LinearEquiv.apply_symm_apply]
  exact nativeTensorSecond_action k R S M N r hr n _

end ArExplicit.ModuleBar

end

end OAI
