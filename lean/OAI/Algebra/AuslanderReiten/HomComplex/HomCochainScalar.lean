import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorHomComplex

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit.ExternalTensor
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable (P : ChainComplex (ModuleCat.{u} R) ℕ)

def canonicalHomCochain (U : ModuleCat.{u} R) : CochainComplex (ModuleCat.{u} k) ℕ :=
  letI := moduleCatBaseModule (k := k) (R := R) U
  letI := moduleCatBaseTower (k := k) (R := R) U
  homCochain k R P U

variable (U : Type u) [AddCommGroup U] [Module R U] [Module k U] [IsScalarTower k R U]

def homCochainScalarEquiv (n : ℕ) :
    (homCochain k R P U).X n ≃ₗ[k] (canonicalHomCochain k R P (ModuleCat.of R U)).X n where
  toFun f := f
  invFun f := f
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a f := by
    change P.X n →ₗ[R] U at f
    apply LinearMap.ext
    intro x
    change a • f x = (algebraMap k R a) • f x
    exact (IsScalarTower.algebraMap_smul R a (f x)).symm

def homCochainScalarIso : homCochain k R P U ≅
    canonicalHomCochain k R P (ModuleCat.of R U) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (homCochainScalarEquiv k R P U n).toModuleIso)
    (fun i j hij => by
      have h : i+1=j := hij
      subst j
      dsimp only [canonicalHomCochain]
      rw [homCochain_d, homCochain_d]
      rfl)

end ArExplicit.ExternalTensor

end

end OAI
