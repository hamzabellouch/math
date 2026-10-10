import Mathlib.RingTheory.TensorProduct.MonoidAlgebra
import Mathlib.RingTheory.TensorProduct.Maps

namespace OAI

/-! # Multiplicative coordinates for tensors of monoid algebras -/

noncomputable section
namespace PolycyclicRecognition

open TensorProduct
open scoped TensorProduct

variable (R M N : Type*) [CommRing R] [Monoid M] [Monoid N]

private def monoidLeft : MonoidAlgebra R M →ₐ[R] MonoidAlgebra R (M × N) :=
  MonoidAlgebra.mapDomainAlgHom R R (MonoidHom.inl M N)

private def monoidRight : MonoidAlgebra R N →ₐ[R] MonoidAlgebra R (M × N) :=
  MonoidAlgebra.mapDomainAlgHom R R (MonoidHom.inr M N)

private theorem monoidLeft_single (m : M) (a : R) :
    monoidLeft R M N (MonoidAlgebra.single m a) = MonoidAlgebra.single (m, 1) a := by
  simp [monoidLeft]

private theorem monoidRight_single (n : N) (a : R) :
    monoidRight R M N (MonoidAlgebra.single n a) = MonoidAlgebra.single (1, n) a := by
  simp [monoidRight]

private theorem monoidLeft_commute_right (p : MonoidAlgebra R M) (q : MonoidAlgebra R N) :
    Commute (monoidLeft R M N p) (monoidRight R M N q) := by
  induction p using MonoidAlgebra.induction_linear with
  | zero => simp
  | add p p' hp hp' => simpa only [map_add] using hp.add_left hp'
  | single m a =>
    induction q using MonoidAlgebra.induction_linear with
    | zero => simp
    | add q q' hq hq' => simpa only [map_add] using hq.add_right hq'
    | single n b =>
      rw [monoidLeft_single, monoidRight_single]
      apply MonoidAlgebra.single_commute_single _ (.all _ _)
      show (m, (1 : N)) * (1, n) = (1, n) * (m, 1)
      simp

def monoidTensorCoordinates :
    MonoidAlgebra R M ⊗[R] MonoidAlgebra R N →ₐ[R] MonoidAlgebra R (M × N) :=
  Algebra.TensorProduct.lift (monoidLeft R M N) (monoidRight R M N)
    (monoidLeft_commute_right R M N)

theorem monoidTensorCoordinates_single (m : M) (a : R) (n : N) (b : R) :
    monoidTensorCoordinates R M N
      (MonoidAlgebra.single m a ⊗ₜ[R] MonoidAlgebra.single n b) =
        MonoidAlgebra.single (m, n) (a * b) := by
  rw [monoidTensorCoordinates, Algebra.TensorProduct.lift_tmul,
    monoidLeft_single, monoidRight_single]
  simp

theorem monoidTensorCoordinates_eq_tensorEquiv
    (x : MonoidAlgebra R M ⊗[R] MonoidAlgebra R N) :
    monoidTensorCoordinates R M N x = MonoidAlgebra.tensorEquiv R x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul p q =>
    induction p using MonoidAlgebra.induction_linear with
    | zero => simp
    | add p p' hp hp' => simp only [add_tmul, map_add, hp, hp']
    | single m a =>
      induction q using MonoidAlgebra.induction_linear with
      | zero => simp
      | add q q' hq hq' => simp only [tmul_add, map_add, hq, hq']
      | single n b =>
        rw [monoidTensorCoordinates_single, MonoidAlgebra.tensorEquiv_single_tmul_single]

theorem monoidTensorCoordinates_injective : Function.Injective (monoidTensorCoordinates R M N) := by
  intro x y h
  apply (MonoidAlgebra.tensorEquiv R).injective
  simpa only [monoidTensorCoordinates_eq_tensorEquiv] using h

theorem monoidTensorCoordinates_tmul_one (p : MonoidAlgebra R M) :
    monoidTensorCoordinates R M N (p ⊗ₜ[R] (1 : MonoidAlgebra R N)) =
      MonoidAlgebra.mapDomain (fun m => (m, (1 : N))) p := by
  rw [monoidTensorCoordinates, Algebra.TensorProduct.lift_tmul, map_one, mul_one]
  rfl

theorem monoidTensorCoordinates_one_tmul (p : MonoidAlgebra R N) :
    monoidTensorCoordinates R M N ((1 : MonoidAlgebra R M) ⊗ₜ[R] p) =
      MonoidAlgebra.mapDomain (fun n => ((1 : M), n)) p := by
  rw [monoidTensorCoordinates, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  rfl

end PolycyclicRecognition

end

end OAI
