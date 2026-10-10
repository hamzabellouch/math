import OAI.GroupTheory.PolycyclicRecognition.Finiteness.ScalarExtendedRepresentationFiniteness
import OAI.GroupTheory.PolycyclicRecognition.Algebra.AbelianH2ExteriorProduct

namespace OAI

/-! # The second-homology cross product over a field

Both variables of the integral cross product are extended by scalars. Its
alternation is proved directly, including in characteristic two.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable (K : Type) [Field K]

def scalarTensorUnit (M : Type) [AddCommGroup M] [Module ℤ M] :
    M →ₗ[ℤ] K ⊗[ℤ] M := TensorProduct.mk ℤ K M 1

def scalarExtensionLinear {M V : Type} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup V] [Module K V] (f : M →ₗ[ℤ] V) : K ⊗[ℤ] M →ₗ[K] V :=
  TensorProduct.AlgebraTensorModule.lift ((LinearMap.id : K →ₗ[K] K).smulRight f)

@[simp] theorem scalarExtensionLinear_tmul {M V : Type} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup V] [Module K V] (f : M →ₗ[ℤ] V) (r : K) (x : M) :
    scalarExtensionLinear K f (r ⊗ₜ[ℤ] x) = r • f x := rfl

def scalarExtensionOperator {M V : Type} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup V] [Module K V] :
    (M →ₗ[ℤ] V) →ₗ[ℤ] (K ⊗[ℤ] M →ₗ[K] V) where
  toFun := scalarExtensionLinear K
  map_add' f g := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro r x
    simp only [scalarExtensionLinear_tmul, LinearMap.add_apply, smul_add]
  map_smul' z f := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro r x
    change r • (z • f x) = z • (r • f x)
    exact smul_comm r z (f x)

variable (A : Type) [CommGroup A]

def abelianH2Bilinear :
    Additive A →ₗ[ℤ] Additive A →ₗ[ℤ] groupHomology.H2 (integralTrivialCoefficient A) where
  toFun x :=
    { toFun := abelianH2Pairing x
      map_add' := (abelianH2Pairing x).map_add
      map_smul' r y := map_intCast_smul (abelianH2Pairing x) ℤ ℤ r y }
  map_add' x y := by
    ext z
    exact congrArg (fun f => f z) (map_add abelianH2Pairing x y)
  map_smul' r x := by
    ext y
    change abelianH2Pairing (r • x) y = r • abelianH2Pairing x y
    exact map_zsmul (abelianH2Pairing.flip y) r x

def scalarH2PairingIntegral :
    Additive A →ₗ[ℤ] Additive A →ₗ[ℤ]
      K ⊗[ℤ] groupHomology.H2 (integralTrivialCoefficient A) where
  toFun x := (scalarTensorUnit K _).comp (abelianH2Bilinear A x)
  map_add' x y := by
    ext z
    change scalarTensorUnit K _ (abelianH2Bilinear A (x + y) z) = _
    rw [map_add, LinearMap.add_apply, map_add]
    rfl
  map_smul' r x := by
    ext y
    change scalarTensorUnit K _ (abelianH2Bilinear A (r • x) y) = _
    rw [map_smul]
    change scalarTensorUnit K _ (r • abelianH2Bilinear A x y) =
      r • scalarTensorUnit K _ (abelianH2Bilinear A x y)
    exact map_zsmul
      (scalarTensorUnit K (groupHomology.H2 (integralTrivialCoefficient A))).toAddMonoidHom
      r (abelianH2Bilinear A x y)

def scalarExtendedH2Pairing :
    (K ⊗[ℤ] Additive A) →ₗ[K] (K ⊗[ℤ] Additive A) →ₗ[K]
      K ⊗[ℤ] groupHomology.H2 (integralTrivialCoefficient A) :=
  scalarExtensionLinear K ((scalarExtensionOperator K).comp (scalarH2PairingIntegral K A))

@[simp] theorem scalarExtendedH2Pairing_tmul (r s : K) (a b : Additive A) :
    scalarExtendedH2Pairing K A (r ⊗ₜ[ℤ] a) (s ⊗ₜ[ℤ] b) =
      (r * s) • scalarTensorUnit K _ (abelianH2Class a.toMul b.toMul) := by
  change r • (s • scalarTensorUnit K _ (abelianH2Class a.toMul b.toMul)) = _
  rw [smul_smul]

theorem scalarExtendedH2Pairing_swap (x y : K ⊗[ℤ] Additive A) :
    scalarExtendedH2Pairing K A x y = -scalarExtendedH2Pairing K A y x := by
  induction x using TensorProduct.inductionOn with
  | tmul r a =>
    induction y using TensorProduct.inductionOn with
    | tmul s b =>
      rw [scalarExtendedH2Pairing_tmul, scalarExtendedH2Pairing_tmul,
        abelianH2Class_swap, map_neg, smul_neg, mul_comm]
    | add y z hy hz =>
      simp only [map_add, LinearMap.add_apply, hy, hz, neg_add_rev]
      abel
  | add x z hx hz =>
    simp only [map_add, LinearMap.add_apply, hx, hz, neg_add_rev]
    abel

theorem scalarExtendedH2Pairing_self (x : K ⊗[ℤ] Additive A) :
    scalarExtendedH2Pairing K A x x = 0 := by
  induction x using TensorProduct.inductionOn with
  | tmul r a => simp only [scalarExtendedH2Pairing_tmul, abelianH2Class_self, map_zero, smul_zero]
  | add x y hx hy =>
    simp only [map_add, LinearMap.add_apply, hx, hy, zero_add, add_zero]
    rw [scalarExtendedH2Pairing_swap K A x y, add_neg_cancel]

def scalarExtendedH2Alternating :
    (K ⊗[ℤ] Additive A) [⋀^Fin 2]→ₗ[K]
      K ⊗[ℤ] groupHomology.H2 (integralTrivialCoefficient A) where
  toFun v := scalarExtendedH2Pairing K A (v 0) (v 1)
  map_update_add' := by
    intro _ v i x y
    fin_cases i <;> simp [Function.update, map_add, LinearMap.add_apply]
  map_update_smul' := by
    intro _ v i r x
    fin_cases i <;> simp [Function.update, map_smul, LinearMap.smul_apply]
  map_eq_zero_of_eq' := by
    intro v i j h hij
    fin_cases i <;> fin_cases j <;>
      simp_all [scalarExtendedH2Pairing_self]

def scalarExtendedH2ExteriorProduct :
    (⋀[K]^2 (K ⊗[ℤ] Additive A)) →ₗ[K]
      K ⊗[ℤ] groupHomology.H2 (integralTrivialCoefficient A) :=
  exteriorPower.alternatingMapLinearEquiv (scalarExtendedH2Alternating K A)

@[simp] theorem scalarExtendedH2ExteriorProduct_value (x y : K ⊗[ℤ] Additive A) :
    scalarExtendedH2ExteriorProduct K A (exteriorPower.ιMulti K 2 ![x, y]) =
      scalarExtendedH2Pairing K A x y :=
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _

end PolycyclicRecognition

end

end OAI
