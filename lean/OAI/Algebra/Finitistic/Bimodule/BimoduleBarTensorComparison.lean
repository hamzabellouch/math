import OAI.Algebra.Finitistic.Bimodule.BimoduleInputFunctor
import OAI.Algebra.Finitistic.Bimodule.BimoduleDerived

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.BimoduleBarComparison
open ExternalTensor.Section4 BimoduleTotal
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]
variable (M : ModuleCat.{u} (Enveloping k B))

abbrev Actions := BimoduleBalancedTensor.Input k B M
attribute [local instance] BimoduleBalancedTensor.inputEnveloping

instance outsideModule : Module B (Actions k B M) :=
  Module.compHom (Actions k B M) (Algebra.TensorProduct.includeLeft : B →ₐ[k] Enveloping k B).toRingHom

instance outsideComm : SMulCommClass B Bᵐᵒᵖ (Actions k B M) where
  smul_comm b r x := by
    change ((b ⊗ₜ[k] (1 : Bᵐᵒᵖ)) • (((1 : B) ⊗ₜ[k] r) • (x : M))) =
      (((1 : B) ⊗ₜ[k] r) • ((b ⊗ₜ[k] (1 : Bᵐᵒᵖ)) • (x : M)))
    rw [← mul_smul,← mul_smul]
    congr 1
    simp only [Algebra.TensorProduct.tmul_mul_tmul,mul_one,one_mul]

instance outsideTower : IsScalarTower k B (Actions k B M) :=
  IsScalarTower.of_algebraMap_smul (by
    intro c x
    change (Algebra.TensorProduct.includeLeft : B →ₐ[k] Enveloping k B) (algebraMap k B c) • (x : M) =
      (Algebra.TensorProduct.includeRight : Bᵐᵒᵖ →ₐ[k] Enveloping k B) (algebraMap k Bᵐᵒᵖ c) • (x : M)
    rw [AlgHom.commutes,AlgHom.commutes])

variable (N : ModuleCat.{u} B)
local instance (N : ModuleCat.{u} B) : Module k N := DerivedBar.BimoduleTensor.scalarModule k B N
local instance (N : ModuleCat.{u} B) : IsScalarTower k B N :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)

abbrev BarTensor := DerivedBar.BimoduleTensor.tensor k B (Actions k B M) N

/-- The field-linear balanced universal map to the bar worker's B-linear quotient. -/
def toBarLinear : InputTensor k B M N →ₗ[k] BarTensor k B M N :=
  BalancedTensor.lift
    ((TensorProduct.mk k (Actions k B M) (BalancedTensor.ScalarLeftModule k B N)).compr₂
      ((DerivedBar.BimoduleTensor.quotient k B (Actions k B M) N).restrictScalars k))
    (by intro b m n; exact DerivedBar.BimoduleTensor.balanced k B (Actions k B M) N m b n)

/-- This comparison retains the actual outside B-action. -/
def toBar : InputTensor k B M N →ₗ[B] BarTensor k B M N where
  __ := (toBarLinear k B M N).toAddMonoidHom
  map_smul' b x := by
    induction x using BalancedTensor.induction_on with
    | hz => simp
    | ht m n =>
      change DerivedBar.BimoduleTensor.quotient k B (Actions k B M) N ((b • m) ⊗ₜ[k] n) =
        b • DerivedBar.BimoduleTensor.quotient k B (Actions k B M) N (m ⊗ₜ[k] n)
      exact (DerivedBar.BimoduleTensor.quotient k B (Actions k B M) N).map_smul b
        ((m : Actions k B M) ⊗ₜ[k] (n : N))
    | ha x y hx hy => simp_all [smul_add]

/-- The reverse unbalanced tensor map is B-linear before passing to the quotient. -/
def fromBarUnbalanced : Actions k B M ⊗[k] (BalancedTensor.ScalarLeftModule k B N) →ₗ[B]
    InputTensor k B M N where
  __ := (TensorProduct.lift (BalancedTensor.mk k B (Actions k B M)
    (BalancedTensor.ScalarLeftModule k B N))).toAddMonoidHom
  map_smul' b x := by
    induction x using TensorProduct.inductionOn with
    | tmul m n => rfl
    | add x y hx hy => simp_all [smul_add]

def fromBar : BarTensor k B M N →ₗ[B] InputTensor k B M N :=
  (DerivedBar.BimoduleTensor.relations k B (Actions k B M) N).liftQ
    (fromBarUnbalanced k B M N) (by
      apply Submodule.span_le.mpr
      rintro z ⟨m,b,n,rfl⟩
      change fromBarUnbalanced k B M N ((MulOpposite.op b • m) ⊗ₜ[k] n - m ⊗ₜ[k] (b • n)) = 0
      exact ((fromBarUnbalanced k B M N).map_sub _ _).trans
        (sub_eq_zero.mpr (BalancedTensor.balance b m n)))

/-- The two independently defined balanced quotients are naturally B-linearly isomorphic. -/
def tensorEquiv : InputTensor k B M N ≃ₗ[B] BarTensor k B M N where
  __ := toBar k B M N
  invFun := fromBar k B M N
  left_inv x := by
    change fromBar k B M N (toBar k B M N x) = x
    induction x using BalancedTensor.induction_on with
    | hz => simp
    | ht m n => rfl
    | ha x y hx hy => simp only [map_add,hx,hy]
  right_inv x := by
    change toBar k B M N (fromBar k B M N x) = x
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      change toBar k B M N (fromBar k B M N
        (DerivedBar.BimoduleTensor.quotient k B (Actions k B M) N x)) =
          DerivedBar.BimoduleTensor.quotient k B (Actions k B M) N x
      induction x using TensorProduct.inductionOn with
      | tmul m n => rfl
      | add x y hx hy =>
        exact (((toBar k B M N).comp ((fromBar k B M N).comp
          (DerivedBar.BimoduleTensor.quotient k B (Actions k B M) N))).map_add x y).trans
          ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm)

/-- Agreement with the exact ordinary bimodule functor used by DerivedBar. -/
def tensorFunctorIso : inputFunctor k B M ≅
    DerivedBar.BimoduleTensor.tensorFunctor k B (Actions k B M) :=
  NatIso.ofComponents (fun N => (tensorEquiv k B M N).toModuleIso) (by
    intro N N' f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using BalancedTensor.induction_on with
    | hz => exact (map_zero _).trans (map_zero _).symm
    | ht m n => rfl
    | ha x y hx hy =>
      exact (map_add _ _ _).trans
        ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm))
end LittleFinitistic.BimoduleBarComparison

end

end OAI
