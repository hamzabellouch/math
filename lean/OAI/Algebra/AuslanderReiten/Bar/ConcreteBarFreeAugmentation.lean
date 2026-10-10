import OAI.Algebra.AuslanderReiten.Bar.ExternalBarTotalFree
import OAI.Algebra.AuslanderReiten.Bar.ExternalBarCyclicCoordinate
import OAI.Algebra.AuslanderReiten.Bar.ConcreteNativeBar
import OAI.Algebra.AuslanderReiten.Evaluation.TensorBeta

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open scoped TensorProduct
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (hq : 1+q ≠ 0)

omit [CharP k 2] in
private theorem coordinate_generator :
    (Resolution.simpleCoordinateEquiv q hq).symm 1 = CocycleData.simpleGenerator q := by
  apply (Resolution.simpleCoordinateEquiv q hq).injective
  rw [LinearEquiv.apply_symm_apply]
  exact (CocycleData.simpleGenerator_coordinate q).symm

omit [CharP k 2] in
theorem tensorCyclicCover_eq_augmentation :
    ExternalTensor.tensorCyclicCover k (T k q) (T k q)
      (Resolution.Simple q) (Resolution.Simple q)
      (Resolution.simpleCoordinateEquiv q hq) (Resolution.simpleCoordinateEquiv q hq) =
      A.augmentation q := by
  apply LinearMap.ext
  intro a
  change a • (show A.Simple q from (Resolution.simpleCoordinateEquiv q hq).symm 1 ⊗ₜ[k]
    (Resolution.simpleCoordinateEquiv q hq).symm 1) = a • A.simpleGenerator q
  rw [coordinate_generator q hq]
  rfl

omit [CharP k 2] in
theorem barCyclicCover_eq_augmentation :
    ExternalTensor.barCyclicCover k (T k q) (T k q)
      (Resolution.Simple q) (Resolution.Simple q)
      (Resolution.simpleCoordinateEquiv q hq) (Resolution.simpleCoordinateEquiv q hq) =
      ModuleCat.ofHom (A.augmentation q) ≫ (nativeToCanonicalSimple q).hom := by
  have h := ExternalTensor.barCyclicCover_eq k (T k q) (T k q)
    (Resolution.Simple q) (Resolution.Simple q)
    (Resolution.simpleCoordinateEquiv q hq) (Resolution.simpleCoordinateEquiv q hq)
  rw [tensorCyclicCover_eq_augmentation q hq] at h
  exact h

def simpleBarFreeCoordinate :=
  ExternalTensor.barTotalFreeCoordinate k (T k q) (T k q)
    (Resolution.Simple q) (Resolution.Simple q)
    (Resolution.simpleCoordinateEquiv q hq) (Resolution.simpleCoordinateEquiv q hq)

theorem simpleBarFreeCoordinate_augmentation :
    simpleBarFreeCoordinate q hq ≫ ModuleCat.ofHom (A.augmentation q) ≫
      (nativeToCanonicalSimple q).hom =
      (ExternalTensor.augmentation k (T k q) (T k q)
        (ModuleBar.nativeResolution k (T k q) (Resolution.Simple q))
        (ModuleBar.nativeResolution k (T k q) (Resolution.Simple q))).f 0 := by
  have h := ExternalTensor.barTotalFreeCoordinate_augmentation k (T k q) (T k q)
    (Resolution.Simple q) (Resolution.Simple q)
    (Resolution.simpleCoordinateEquiv q hq) (Resolution.simpleCoordinateEquiv q hq)
  rw [barCyclicCover_eq_augmentation q hq] at h
  exact h

end ArExplicit.T

end

end OAI
