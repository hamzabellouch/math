import OAI.GroupTheory.PolycyclicRecognition.Algebra.NormalQuotientCoordinates
import Mathlib.RepresentationTheory.Induced

namespace OAI

/-! # Direct-sum coordinates for induction from a normal subgroup

The coordinates give a linear equivalence, used below with integral coefficients. The group
action remains the induced action; no invariance of the chosen section is
asserted.
-/

noncomputable section
namespace PolycyclicRecognition

open Representation
open scoped MonoidAlgebra TensorProduct
attribute [local instance 2000] Rep.hV2

variable (k : Type) [CommRing k] {G : Type} [Group G]
  (N : Subgroup G) [N.Normal] (A : Rep k N)

def inductionTensorCoordinates :
    k[G] ⊗[k] A →ₗ[k] ((G ⧸ N) →₀ A) :=
  TensorProduct.lift <|
    (Finsupp.lift _ _ _ fun g =>
      (Finsupp.lsingle (QuotientGroup.mk' N g)).comp (A.ρ (normalQuotientPart N g)⁻¹))
      ∘ₗ (MonoidAlgebra.coeffLinearEquiv k).toLinearMap

@[simp] theorem inductionTensorCoordinates_single (g : G) (a : A) :
    inductionTensorCoordinates k N A (MonoidAlgebra.single g 1 ⊗ₜ[k] a) =
      Finsupp.single (QuotientGroup.mk' N g) (A.ρ (normalQuotientPart N g)⁻¹ a) := by
  simp [inductionTensorCoordinates]

theorem inductionTensorCoordinates_invariant (n : N) :
    inductionTensorCoordinates k N A ∘ₗ
      (Representation.tprod ((Representation.leftRegular k G).comp N.subtype) A.ρ) n =
      inductionTensorCoordinates k N A := by
  apply TensorProduct.ext
  apply MonoidAlgebra.lhom_ext'
  intro g
  apply LinearMap.ext_ring
  apply LinearMap.ext
  intro a
  simp [map_mul, mul_inv_rev, Module.End.mul_apply]
  congr 1
  change QuotientGroup.mk' N ((n : G) * g) = QuotientGroup.mk' N g
  rw [map_mul, normalQuotient_mk_subgroup, one_mul]

def inductionCoordinates : Rep.ind N.subtype A →ₗ[k] ((G ⧸ N) →₀ A) :=
  Coinvariants.lift _ (inductionTensorCoordinates k N A)
    (inductionTensorCoordinates_invariant k N A)

@[simp] theorem inductionCoordinates_mk (g : G) (a : A) :
    inductionCoordinates k N A (IndV.mk N.subtype A.ρ g a) =
      Finsupp.single (QuotientGroup.mk' N g) (A.ρ (normalQuotientPart N g)⁻¹ a) := by
  exact inductionTensorCoordinates_single k N A g a

def inductionCoordinatesInv : ((G ⧸ N) →₀ A) →ₗ[k] Rep.ind N.subtype A :=
  Finsupp.lsum k fun c => IndV.mk N.subtype A.ρ (normalQuotientRepresentative N c)

@[simp] theorem inductionCoordinatesInv_single (c : G ⧸ N) (a : A) :
    inductionCoordinatesInv k N A (Finsupp.single c a) =
      IndV.mk N.subtype A.ρ (normalQuotientRepresentative N c) a := by
  simp [inductionCoordinatesInv]

theorem inductionCoordinates_right_inv :
    (inductionCoordinates k N A).comp (inductionCoordinatesInv k N A) = LinearMap.id := by
  apply Finsupp.lhom_ext'
  intro c
  apply LinearMap.ext
  intro a
  change inductionCoordinates k N A (inductionCoordinatesInv k N A (Finsupp.single c a)) = _
  rw [inductionCoordinatesInv_single, inductionCoordinates_mk,
    normalQuotientRepresentative_mk, normalQuotientPart_representative]
  simp

theorem inductionCoordinates_left_inv :
    (inductionCoordinatesInv k N A).comp (inductionCoordinates k N A) = LinearMap.id := by
  apply IndV.hom_ext
  intro g
  apply LinearMap.ext
  intro a
  change inductionCoordinatesInv k N A
    (inductionCoordinates k N A (IndV.mk N.subtype A.ρ g a)) = IndV.mk N.subtype A.ρ g a
  rw [inductionCoordinates_mk, inductionCoordinatesInv_single]
  change Coinvariants.mk (Representation.tprod ((Representation.leftRegular k G).comp N.subtype) A.ρ)
    (MonoidAlgebra.single (normalQuotientRepresentative N (QuotientGroup.mk' N g)) (1 : k) ⊗ₜ[k]
      A.ρ (normalQuotientPart N g)⁻¹ a) =
    Coinvariants.mk (Representation.tprod ((Representation.leftRegular k G).comp N.subtype) A.ρ)
      (MonoidAlgebra.single g (1 : k) ⊗ₜ[k] a)
  rw [Coinvariants.mk_tmul_inv]
  simp only [MonoidHom.comp_apply, Representation.leftRegular, Representation.ofMulAction_single,
    Subgroup.subtype_apply, smul_eq_mul, normalQuotientPart_decompose]

def normalInductionEquiv : Rep.ind N.subtype A ≃ₗ[k] ((G ⧸ N) →₀ A) :=
  LinearEquiv.ofLinearMap (inductionCoordinates k N A) (inductionCoordinatesInv k N A)
    (inductionCoordinates_right_inv k N A) (inductionCoordinates_left_inv k N A)

end PolycyclicRecognition

end

end OAI
