import OAI.Algebra.AuslanderReiten.Algebras.TensorSimple
import OAI.Algebra.AuslanderReiten.Bar.TCasimirSquare

namespace OAI

noncomputable section
open scoped TensorProduct

namespace ArExplicit.A

variable {k : Type*} [Field k] (q : k)

@[simp] theorem simpleCoordinate_zero : simpleCoordinate q (0 : Simple q) = 0 := by
  change simpleCoordinate q (0 : Resolution.Simple q ⊗[k] Resolution.Simple q) = 0
  exact map_zero _

def augmentation : A k q →ₗ[A k q] Simple q where
  toFun a := a • simpleGenerator q
  map_add' a b := add_smul a b _
  map_smul' a b := mul_smul a b _

theorem augmentation_surjective (hq1 : 1 + q ≠ 0) : Function.Surjective (augmentation q) := by
  intro x
  refine ⟨algebraMap k (A k q) (simpleCoordinate q x), ?_⟩
  apply simpleCoordinate_injective q hq1
  change simpleCoordinate q ((algebraMap k (A k q) (simpleCoordinate q x)) • simpleGenerator q) = _
  rw [simpleCoordinate_smul, simpleGenerator_coordinate, mul_one, AlgHom.commutes]
  rfl

theorem augmentation_kernel (hq1 : 1 + q ≠ 0) :
    LinearMap.ker (augmentation q) = augmentationIdeal q := by
  ext a
  change augmentation q a = 0 ↔ simpleCharacter q a = 0
  constructor
  · intro h
    have hh := congrArg (simpleCoordinate q) h
    change simpleCoordinate q (a • simpleGenerator q) = simpleCoordinate q (0 : Simple q) at hh
    simpa only [simpleCoordinate_smul, simpleGenerator_coordinate, mul_one, simpleCoordinate_zero] using hh
  · intro h
    apply simpleCoordinate_injective q hq1
    change simpleCoordinate q (a • simpleGenerator q) = simpleCoordinate q (0 : Simple q)
    rw [simpleCoordinate_smul, h, zero_mul, simpleCoordinate_zero]

def betaDetector : A k q →ₗ[k] k :=
  (TensorProduct.lid k k).toLinearMap.comp
    (TensorProduct.map (T.coefficient q (true, .f)) (T.coefficient q (true, .f)))

@[simp] theorem betaDetector_socle :
    betaDetector q (T.upper q .f ⊗ₜ[k] T.upper q .f) = 1 := by
  simp [betaDetector]

theorem beta_ne_zero : beta q ≠ 0 := by
  intro h
  have hh := congrArg (fun z : augmentationIdeal q => betaDetector q z.val)
    (DFunLike.congr_fun h (simpleGenerator q))
  change betaDetector q (socleMap q (simpleGenerator q)) = 0 at hh
  rw [socleMap_generator, betaDetector_socle] at hh
  exact one_ne_zero hh

theorem beta_stable_ne_zero (hq1 : 1 + q ≠ 0) :
    StableHom.classOf (A k q) (Simple q) (augmentationIdeal q) (beta q) ≠ 0 :=
  (AFrobeniusTrace k q).stable_class_ne_zero (A_trace_symmetric k q) (augmentationIdeal q)
    (augmentationIdeal_annihilates q hq1) (augmentationIdeal q).subtype Subtype.val_injective
    (fun x => x.property) (beta_ne_zero q)

end ArExplicit.A

end

end OAI
