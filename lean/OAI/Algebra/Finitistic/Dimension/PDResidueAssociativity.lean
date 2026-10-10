import OAI.Algebra.Finitistic.Dimension.PDResidueProjection
import OAI.Algebra.Finitistic.Dimension.PDBarTensorComparison

namespace OAI
noncomputable section
open CategoryTheory TensorProduct
open scoped TensorProduct
namespace LittleFinitistic.PDResidueAssociativity
universe u
variable {k A D : Type u} [Field k] [Ring A] [Algebra k A] [Ring D] [Algebra k D]
variable (f : A →ₐ[k] D)
variable (V : Type u) [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
local notation "S" => PDTensor.Residue (A := D)
local notation "SA" => PDResidueProjection.InflatedResidue f
local notation "T" => BalancedTensor.Tensor k A SA V
local notation "DV" => DerivedBar.Balanced.tensor f V

def coefficient (s : S) : PDBarQuotient.RightBase f →ₗ[k] V →ₗ[k] T where
  toFun d := BalancedTensor.mk k A SA V (MulOpposite.op (show D from d) • s)
  map_add' a b := by
    ext v
    exact (congrArg (fun x : SA => BalancedTensor.mk k A SA V x v)
      (add_smul (MulOpposite.op (show D from a))
        (MulOpposite.op (show D from b)) s)).trans
      (LinearMap.congr_fun ((BalancedTensor.mk k A SA V).map_add _ _) v)
  map_smul' c d := by
    ext v
    change BalancedTensor.mk k A SA V (MulOpposite.op (c • (show D from d)) • s) v = _
    rw [MulOpposite.op_smul, smul_assoc]
    exact LinearMap.congr_fun ((BalancedTensor.mk k A SA V).map_smul c _) v

def inner (s : S) : DV →ₗ[k] T :=
  (BalancedTensor.lift (coefficient f V s) (by
    intro a d v
    change BalancedTensor.mk k A SA V (MulOpposite.op ((show D from d)*f a) • s) v =
      BalancedTensor.mk k A SA V (MulOpposite.op (show D from d) • s) (a • v)
    rw [MulOpposite.op_mul, mul_smul]
    exact BalancedTensor.balance (k := k) (M := SA) a _ v)).comp (PDBarQuotient.inverse f V)

omit [IsScalarTower k A V] in
@[simp] theorem inner_mk (s : S) (d : D) (v : V) :
    inner f V s (DerivedBar.Balanced.quotient f V (d ⊗ₜ[k] v)) =
      BalancedTensor.mk k A SA V (MulOpposite.op d • s) v := rfl

def pair : S →ₗ[k] DV →ₗ[k] T where
  toFun := inner f V
  map_add' s t := by
    apply ((DerivedBar.Balanced.relations f V).restrictScalars k).linearMap_qext
    apply TensorProduct.ext
    ext d v
    change BalancedTensor.mk k A SA V (MulOpposite.op d • (s+t)) v =
      BalancedTensor.mk k A SA V (MulOpposite.op d • s) v + BalancedTensor.mk k A SA V (MulOpposite.op d • t) v
    rw [smul_add]
    exact LinearMap.congr_fun ((BalancedTensor.mk k A SA V).map_add _ _) v
  map_smul' c s := by
    apply ((DerivedBar.Balanced.relations f V).restrictScalars k).linearMap_qext
    apply TensorProduct.ext
    ext d v
    change BalancedTensor.mk k A SA V (MulOpposite.op d • (c • s)) v =
      c • BalancedTensor.mk k A SA V (MulOpposite.op d • s) v
    rw [smul_comm]
    exact LinearMap.congr_fun ((BalancedTensor.mk k A SA V).map_smul c _) v

def forward : BalancedTensor.Tensor k D S DV →ₗ[k] T :=
  BalancedTensor.lift (pair f V) (by
    intro d s z
    induction z using Submodule.Quotient.induction_on with
    | _ z =>
      induction z using TensorProduct.inductionOn with
      | tmul b v =>
        change inner f V (MulOpposite.op d • s) (DerivedBar.Balanced.quotient f V (b ⊗ₜ[k] v)) =
          inner f V s (d • DerivedBar.Balanced.quotient f V (b ⊗ₜ[k] v))
        rw [inner_mk, ← LinearMap.map_smul, TensorProduct.smul_tmul', inner_mk]
        rw [← mul_smul, ← MulOpposite.op_mul]
        rfl
      | add x y hx hy => simpa only [Submodule.Quotient.mk_add, map_add, smul_add] using congrArg₂ (·+·) hx hy)

def unit : V →ₗ[k] DV :=
  ((DerivedBar.Balanced.quotient f V).restrictScalars k).comp (TensorProduct.mk k D V 1)

def inverse : T →ₗ[k] BalancedTensor.Tensor k D S DV :=
  BalancedTensor.lift ((BalancedTensor.mk k D S DV).compl₁₂ LinearMap.id (unit f V)) (by
    intro a s v
    change BalancedTensor.mk k D S DV (MulOpposite.op (f a) • s) (unit f V v) =
      BalancedTensor.mk k D S DV s (unit f V (a • v))
    erw [BalancedTensor.balance (k := k) (A := D) (M := S) (N := DV)
      (f a) (show S from s) (unit f V v)]
    congr 1
    change f a • DerivedBar.Balanced.quotient f V ((1 : D) ⊗ₜ[k] v) =
      DerivedBar.Balanced.quotient f V ((1 : D) ⊗ₜ[k] (a • v))
    rw [← LinearMap.map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    simpa only [one_mul] using DerivedBar.Balanced.balanced f V (1 : D) a v)

omit [IsScalarTower k A V] in
@[simp] theorem inverse_mk (s : SA) (v : V) :
    inverse f V (BalancedTensor.mk k A SA V s v) = BalancedTensor.mk k D S DV s (unit f V v) := rfl

/-- Actual balanced associativity S tensor_D (D tensor_A V) = S tensor_A V,
with the right A action restricted along f. -/
def equiv : BalancedTensor.Tensor k D S DV ≃ₗ[k] T :=
  LinearEquiv.ofLinearMap (forward f V) (inverse f V) (by
    apply BalancedTensor.ext
    intro s v
    change BalancedTensor.mk k A SA V (MulOpposite.op (1 : D) • s) v = _
    rw [MulOpposite.op_one, one_smul]
    rfl) (by
    apply BalancedTensor.ext
    intro s z
    induction z using Submodule.Quotient.induction_on with
    | _ z =>
      induction z using TensorProduct.inductionOn with
      | tmul d v =>
        change BalancedTensor.mk k D S DV (MulOpposite.op d • s) (unit f V v) =
          BalancedTensor.mk k D S DV s (DerivedBar.Balanced.quotient f V (d ⊗ₜ[k] v))
        rw [BalancedTensor.balance]
        congr 1
        change d • DerivedBar.Balanced.quotient f V ((1 : D) ⊗ₜ[k] v) = _
        rw [← LinearMap.map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      | add x y hx hy => simpa only [Submodule.Quotient.mk_add, map_add] using congrArg₂ (·+·) hx hy)
end LittleFinitistic.PDResidueAssociativity

end

end OAI
