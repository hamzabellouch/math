import OAI.Algebra.AuslanderReiten.Bar.BarBalancedEquiv
import OAI.Algebra.AuslanderReiten.Bar.BarBalancedSuffix
import OAI.Algebra.AuslanderReiten.Tensor.EnvelopingBalancedMap

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace ArExplicit.BarBalanced
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
attribute [local instance 2000] AbsoluteBar.baseModule AbsoluteBar.bimoduleTower

def differential (n : ℕ) : evaluated k R M (n+1) →ₗ[R] evaluated k R M n :=
  EnvelopingBimodule.tensorMap (ModuleCat.of R M)
    (ModuleCat.ofHom (X := AbsoluteBar.moduleObject k R (n+1))
      (Y := AbsoluteBar.moduleObject k R n) (AbsoluteBar.differential k R n))

omit [IsScalarTower k R M] in
@[simp] theorem differential_tmul (n : ℕ) (x : bar k R (n+1)) (m : M) :
    differential k R M n (BalancedTensor.tmul x m) =
      BalancedTensor.tmul (EnvelopingBimodule.map
        (ModuleCat.ofHom (X := AbsoluteBar.moduleObject k R (n+1))
      (Y := AbsoluteBar.moduleObject k R n) (AbsoluteBar.differential k R n)) x) m := rfl

theorem equiv_differential (n : ℕ) (z : evaluated k R M (n+1)) :
    equiv k R M n (differential k R M n z) =
      ModuleBar.differential k R M n (equiv k R M (n+1) z) := by
  induction z using BalancedTensor.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x m =>
    rw [differential_tmul, equiv_tmul, equiv_tmul]
    exact rawEval_boundary k R M n (coordinates k R (n+1) x) m

def cubic (p : AbsoluteBar.Cochain3 k R) (n : ℕ) :
    evaluated k R M (n+4) →ₗ[R] evaluated k R M (n+1) :=
  EnvelopingBimodule.tensorMap (ModuleCat.of R M)
    (ModuleCat.ofHom (X := AbsoluteBar.moduleObject k R (n+4))
      (Y := AbsoluteBar.moduleObject k R (n+1)) (AbsoluteBar.suffixComparisonMap k R p n))

omit [IsScalarTower k R M] in
@[simp] theorem cubic_tmul (p : AbsoluteBar.Cochain3 k R) (n : ℕ)
    (x : bar k R (n+4)) (m : M) :
    cubic k R M p n (BalancedTensor.tmul x m) =
      BalancedTensor.tmul (EnvelopingBimodule.map
        (ModuleCat.ofHom (X := AbsoluteBar.moduleObject k R (n+4))
      (Y := AbsoluteBar.moduleObject k R (n+1)) (AbsoluteBar.suffixComparisonMap k R p n)) x) m := rfl

theorem equiv_cubic (p : AbsoluteBar.Cochain3 k R) (n : ℕ)
    (z : evaluated k R M (n+4)) :
    equiv k R M (n+1) (cubic k R M p n z) =
      ModuleBar.suffixComparisonMap k R M p n (equiv k R M (n+4) z) := by
  induction z using BalancedTensor.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x m =>
    rw [cubic_tmul, equiv_tmul, equiv_tmul]
    exact rawEval_suffix k R M p (n+1) (coordinates k R (n+4) x) m

variable [CharP k 2]

def complex : ChainComplex (ModuleCat.{u} R) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of R (evaluated k R M (n+1)))
    (fun n => ModuleCat.ofHom (differential k R M (n+1)))
    (fun n => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      apply (equiv k R M (n+1)).injective
      change equiv k R M (n+1)
        (differential k R M (n+1) (differential k R M (n+2) z)) =
          equiv k R M (n+1) 0
      rw [equiv_differential, equiv_differential, map_zero]
      exact ModuleBar.boundary_squared k R M (n+1) _)

@[simp] theorem complex_d (n : ℕ) : (complex k R M).d (n+1) n =
    ModuleCat.ofHom (differential k R M (n+1)) := by
  simp only [complex, ChainComplex.of.d]
  apply Category.id_comp

def complexIso : complex k R M ≅ ModuleBar.complex k R M :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (equiv k R M (n+1)).toModuleIso)
    (fun i j hij => by
      have h : j+1 = i := hij
      subst i
      rw [complex_d, ModuleBar.complex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      exact (equiv_differential k R M (j+1) z).symm)

end ArExplicit.BarBalanced

end

end OAI
