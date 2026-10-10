import OAI.Algebra.AuslanderReiten.Duality.DualTensorModule
import OAI.Algebra.AuslanderReiten.Tensor.BalancedTensorCategory

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit.DualTensor
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable (P : ChainComplex (ModuleCat.{u} R) ℕ)

def dualHomObject (n : ℕ) : ModuleCat.{u} R :=
  ModuleCat.of R (RightDual k R (P.X n →ₗ[R] R))

def dualHomDifferential (n : ℕ) :
    dualHomObject (k := k) P (n + 1) ⟶ dualHomObject (k := k) P n :=
  ModuleCat.ofHom (RightDual.map (precomposeRight (P.d (n + 1) n).hom))

theorem dualHomDifferential_comp (n : ℕ) :
    dualHomDifferential (k := k) P (n + 1) ≫ dualHomDifferential (k := k) P n = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply RightDual.ext
  apply LinearMap.ext
  intro f
  change φ.functional ((f.comp (P.d (n + 1) n).hom).comp (P.d (n + 2) (n + 1)).hom) = 0
  have hd : (P.d (n + 1) n).hom.comp (P.d (n + 2) (n + 1)).hom = 0 :=
    congrArg ModuleCat.Hom.hom (P.d_comp_d (n + 2) (n + 1) n)
  rw [LinearMap.comp_assoc, hd, LinearMap.comp_zero, map_zero]

def dualHomComplex : ChainComplex (ModuleCat.{u} R) ℕ :=
  ChainComplex.of (dualHomObject (k := k) P) (dualHomDifferential (k := k) P)
    (dualHomDifferential_comp (k := k) P)

theorem dualHomComplex_d (n : ℕ) :
    (dualHomComplex (k := k) P).d (n + 1) n = dualHomDifferential (k := k) P n := by
  exact ChainComplex.of_d _ _ _

def tensorComplex : ChainComplex (ModuleCat.{u} R) ℕ :=
  ((BalancedTensor.functor (k := k) (R := R) (S := R) (F := Coinduced k R)).mapHomologicalComplex _).obj P

def complexIso [∀ n, Module.Finite R (P.X n)] [∀ n, Module.Projective R (P.X n)] :
    tensorComplex (k := k) P ≅ dualHomComplex (k := k) P :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (moduleEvaluationEquiv (k := k) (R := R) (V := P.X n)).toModuleIso)
    (by
      intro i j hij
      obtain rfl : i = j + 1 := by simpa using hij.symm
      rw [dualHomComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      exact (moduleEvaluation_natural (P.d (j + 1) j).hom z).symm)

end ArExplicit.DualTensor

end

end OAI
