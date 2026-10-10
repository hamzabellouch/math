import OAI.GroupTheory.PolycyclicRecognition.Algebra.ScalarHigherExteriorProduct
import OAI.GroupTheory.PolycyclicRecognition.Algebra.TupleBarDeterminant
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.AbelianMultilinearHomology
import Mathlib.LinearAlgebra.ExteriorPower.Basis

namespace OAI

/-! # Coordinate cochains detect the higher exterior cross product -/

noncomputable section
namespace PolycyclicRecognition
open scoped TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable (K A : Type) [Field K] [CommGroup A]

def scalarHigherDetectorCoefficients {n : ℕ}
    (f : Fin n → Module.Dual K (K ⊗[ℤ] Additive A)) :
    MultilinearMap ℤ (fun _ : Fin n => Additive A) K :=
  (MultilinearMap.mkPiAlgebra ℤ (Fin n) K).compLinearMap
    (fun i => ((f i).restrictScalars ℤ).comp (scalarTensorUnit K (Additive A)))

def scalarHigherDetector {n : ℕ}
    (f : Fin n → Module.Dual K (K ⊗[ℤ] Additive A)) :
    (K ⊗[ℤ] groupHomology (integralTrivialCoefficient A) n) →ₗ[K] K :=
  scalarExtensionLinear K (abelianMultilinearHomology (scalarHigherDetectorCoefficients K A f))

theorem scalarHigherDetector_class {n : ℕ}
    (f : Fin (n + 1) → Module.Dual K (K ⊗[ℤ] Additive A))
    (v : Fin (n + 1) → Additive A) :
    scalarHigherDetector K A f (scalarTensorUnit K _ (tupleBarAdditiveClass A v)) =
      Matrix.det (fun i j => f i (scalarTensorUnit K _ (v j))) := by
  change (1 : K) • abelianMultilinearHomology (scalarHigherDetectorCoefficients K A f)
    (tupleBarProductClass (fun i => (v i).toMul)) = _
  rw [one_smul, tupleBarProductClass, abelianMultilinearHomology_π]
  change abelianMultilinearChains (scalarHigherDetectorCoefficients K A f)
    (groupHomology.iCycles (integralTrivialCoefficient A) (n + 1)
      (tupleBarProductCycle (fun i => (v i).toMul))) = _
  rw [tupleBarProductCycle_val]
  change tupleBarEvaluation (fun i a => f i (scalarTensorUnit K _ (Additive.ofMul a)))
    (tupleBarProduct (fun i => (v i).toMul)) = _
  exact tupleBarEvaluation_product _ _

theorem scalarHigherDetector_exterior {n : ℕ}
    (f : Fin (n + 1) → Module.Dual K (K ⊗[ℤ] Additive A)) :
    (scalarHigherDetector K A f).comp (scalarHigherExteriorProduct K A n) =
      exteriorPower.pairingDual K (K ⊗[ℤ] Additive A) (n + 1)
        (exteriorPower.ιMulti K (n + 1) f) := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.coe_multilinearMap_injective
  apply tensorMultilinear_ext
  intro v
  change scalarHigherDetector K A f
      (scalarHigherExteriorProduct K A n
        (exteriorPower.ιMulti K (n + 1) (fun i => scalarTensorUnit K _ (v i)))) =
    exteriorPower.pairingDual K (K ⊗[ℤ] Additive A) (n + 1)
      (exteriorPower.ιMulti K (n + 1) f)
      (exteriorPower.ιMulti K (n + 1) (fun i => scalarTensorUnit K _ (v i)))
  rw [scalarHigherExteriorProduct_value, scalarHigherBarAlternating_unit,
    scalarHigherDetector_class, exteriorPower.pairingDual_ιMulti_ιMulti]
  exact (Matrix.det_transpose (Matrix.of (fun i j => f i (scalarTensorUnit K _ (v j))))).symm

theorem scalarHigherExteriorProduct_injective (n : ℕ) :
    Function.Injective (scalarHigherExteriorProduct K A n) := by
  classical
  let b := Module.Free.chooseBasis K (K ⊗[ℤ] Additive A)
  let : LinearOrder (Module.Free.ChooseBasisIndex K (K ⊗[ℤ] Additive A)) :=
    linearOrderOfSTO WellOrderingRel
  intro x y hxy
  apply (b.exteriorPower (n + 1)).repr.injective
  apply Finsupp.ext
  intro s
  rw [exteriorPower.basis_repr_apply, exteriorPower.basis_repr_apply]
  let f : Fin (n + 1) → Module.Dual K (K ⊗[ℤ] Additive A) :=
    b.coord ∘ Set.powersetCard.ofFinEmbEquiv.symm s
  have h := congrArg (scalarHigherDetector K A f) hxy
  have he := scalarHigherDetector_exterior K A f
  exact (LinearMap.congr_fun he x).symm.trans (h.trans (LinearMap.congr_fun he y))

end PolycyclicRecognition

end

end OAI
