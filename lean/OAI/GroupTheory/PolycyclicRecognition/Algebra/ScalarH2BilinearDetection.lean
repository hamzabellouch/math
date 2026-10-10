import OAI.GroupTheory.PolycyclicRecognition.Algebra.ScalarExtendedH2CrossProduct
import Mathlib.LinearAlgebra.ExteriorPower.Basis

namespace OAI

/-! # Bilinear coordinates detect the scalar-extended exterior cross product -/

noncomputable section
namespace PolycyclicRecognition
open scoped TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable (K A : Type) [Field K] [CommGroup A]

def scalarH2DetectorPairing
    (B : (K ⊗[ℤ] Additive A) →ₗ[K] (K ⊗[ℤ] Additive A) →ₗ[K] K) :
    Additive A →+ Additive A →+ K where
  toFun a :=
    { toFun b := B (scalarTensorUnit K _ a) (scalarTensorUnit K _ b)
      map_zero' := by simp
      map_add' x y := by simp }
  map_zero' := by ext x; simp
  map_add' x y := by ext z; simp

def scalarH2Detector
    (B : (K ⊗[ℤ] Additive A) →ₗ[K] (K ⊗[ℤ] Additive A) →ₗ[K] K) :
    (K ⊗[ℤ] groupHomology.H2 (integralTrivialCoefficient A)) →ₗ[K] K :=
  scalarExtensionLinear K (bilinearPairingHomology (scalarH2DetectorPairing K A B))

theorem scalarH2Detector_class
    (B : (K ⊗[ℤ] Additive A) →ₗ[K] (K ⊗[ℤ] Additive A) →ₗ[K] K) (a b : A) :
    scalarH2Detector K A B (scalarTensorUnit K _ (abelianH2Class a b)) =
      B (scalarTensorUnit K _ (Additive.ofMul a)) (scalarTensorUnit K _ (Additive.ofMul b)) -
      B (scalarTensorUnit K _ (Additive.ofMul b)) (scalarTensorUnit K _ (Additive.ofMul a)) := by
  change (1 : K) • bilinearPairingHomology (scalarH2DetectorPairing K A B)
    (abelianH2Class a b) = _
  rw [one_smul, abelianH2Class, bilinearPairingHomology_π]
  change bilinearPairingChains (scalarH2DetectorPairing K A B)
    (Finsupp.single (a, b) 1 - Finsupp.single (b, a) 1) = _
  rw [map_sub, bilinearPairingChains_single, bilinearPairingChains_single,
    one_smul, one_smul]
  rfl

theorem scalarH2Detector_pairing
    (B : (K ⊗[ℤ] Additive A) →ₗ[K] (K ⊗[ℤ] Additive A) →ₗ[K] K)
    (x y : K ⊗[ℤ] Additive A) :
    scalarH2Detector K A B (scalarExtendedH2Pairing K A x y) = B x y - B y x := by
  induction x using TensorProduct.inductionOn with
  | tmul r a =>
    induction y using TensorProduct.inductionOn with
    | tmul s b =>
      rw [scalarExtendedH2Pairing_tmul, map_smul, scalarH2Detector_class]
      have ht (t : K) (c : Additive A) : t ⊗ₜ[ℤ] c = t • scalarTensorUnit K _ c := by
        change t ⊗ₜ[ℤ] c = t • ((1 : K) ⊗ₜ[ℤ] c)
        simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [ht r a, ht s b]
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
      change r * s * (B (scalarTensorUnit K _ a) (scalarTensorUnit K _ b) -
        B (scalarTensorUnit K _ b) (scalarTensorUnit K _ a)) = _
      ring
    | add y z hy hz =>
      simp only [map_add, LinearMap.add_apply, hy, hz]
      ring
  | add x z hx hz =>
    simp only [map_add, LinearMap.add_apply, hx, hz]
    ring

theorem scalarH2Detector_exterior (f : Fin 2 → Module.Dual K (K ⊗[ℤ] Additive A)) :
    (scalarH2Detector K A ((f 0).smulRight (f 1))).comp
        (scalarExtendedH2ExteriorProduct K A) =
      exteriorPower.pairingDual K (K ⊗[ℤ] Additive A) 2 (exteriorPower.ιMulti K 2 f) := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  have hv : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply]
  rw [hv,
    scalarExtendedH2ExteriorProduct_value, scalarH2Detector_pairing,
    exteriorPower.pairingDual_ιMulti_ιMulti]
  simp only [LinearMap.smulRight_apply, LinearMap.smul_apply, smul_eq_mul,
    Matrix.det_fin_two, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  ring

theorem scalarExtendedH2ExteriorProduct_injective :
    Function.Injective (scalarExtendedH2ExteriorProduct K A) := by
  classical
  let b := Module.Free.chooseBasis K (K ⊗[ℤ] Additive A)
  let : LinearOrder (Module.Free.ChooseBasisIndex K (K ⊗[ℤ] Additive A)) :=
    linearOrderOfSTO WellOrderingRel
  intro x y hxy
  apply (b.exteriorPower 2).repr.injective
  apply Finsupp.ext
  intro s
  rw [exteriorPower.basis_repr_apply, exteriorPower.basis_repr_apply]
  let f : Fin 2 → Module.Dual K (K ⊗[ℤ] Additive A) :=
    b.coord ∘ Set.powersetCard.ofFinEmbEquiv.symm s
  have h := congrArg (scalarH2Detector K A ((f 0).smulRight (f 1))) hxy
  have he := scalarH2Detector_exterior K A f
  exact (LinearMap.congr_fun he x).symm.trans (h.trans (LinearMap.congr_fun he y))

end PolycyclicRecognition

end

end OAI
