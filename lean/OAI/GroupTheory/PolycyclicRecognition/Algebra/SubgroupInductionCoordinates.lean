import Mathlib.RepresentationTheory.Induced
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NormalInductionCoordinates

namespace OAI

/-! # Direct-sum coordinates for induction from an arbitrary subgroup

Right cosets, with a chosen representative, are sufficient. No normality of
the subgroup is required for exact induction or for the rational base case.
-/
noncomputable section
namespace PolycyclicRecognition
open Representation
open scoped MonoidAlgebra TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G] (H : Subgroup G)

abbrev subgroupRightCosets := Quotient (QuotientGroup.rightRel H)
def subgroupRightCoset (g : G) : subgroupRightCosets H := Quotient.mk _ g
def subgroupRightRepresentative (c : subgroupRightCosets H) : G := c.out

@[simp]
theorem subgroupRightRepresentative_coset (c : subgroupRightCosets H) :
    subgroupRightCoset H (subgroupRightRepresentative H c) = c := Quotient.out_eq _

@[simp]
theorem subgroupRightCoset_mul (h : H) (g : G) :
    subgroupRightCoset H ((h : G) * g) = subgroupRightCoset H g := by
  apply Quotient.sound
  exact (QuotientGroup.rightRel_apply).mpr (by simp)

def subgroupRightPart (g : G) : H :=
  ⟨g * (subgroupRightRepresentative H (subgroupRightCoset H g))⁻¹,
    (QuotientGroup.rightRel_apply).mp
      (Quotient.exact (subgroupRightRepresentative_coset H (subgroupRightCoset H g)))⟩

@[simp]
theorem subgroupRightPart_decompose (g : G) :
    (subgroupRightPart H g : G) * subgroupRightRepresentative H (subgroupRightCoset H g) = g := by
  simp [subgroupRightPart]

@[simp]
theorem subgroupRightPart_mul (h : H) (g : G) :
    subgroupRightPart H ((h : G) * g) = h * subgroupRightPart H g := by
  apply Subtype.ext
  simp [subgroupRightPart, mul_assoc]

@[simp]
theorem subgroupRightPart_representative (c : subgroupRightCosets H) :
    subgroupRightPart H (subgroupRightRepresentative H c) = 1 := by
  apply Subtype.ext
  simp [subgroupRightPart]

variable (k : Type) [CommRing k] (A : Rep k H)

def subgroupInductionTensorCoordinates :
    k[G] ⊗[k] A →ₗ[k] (subgroupRightCosets H →₀ A) :=
  TensorProduct.lift <|
    (Finsupp.lift _ _ _ fun g =>
      (Finsupp.lsingle (subgroupRightCoset H g)).comp (A.ρ (subgroupRightPart H g)⁻¹))
      ∘ₗ (MonoidAlgebra.coeffLinearEquiv k).toLinearMap

@[simp]
theorem subgroupInductionTensorCoordinates_single (g : G) (a : A) :
    subgroupInductionTensorCoordinates H k A (MonoidAlgebra.single g 1 ⊗ₜ[k] a) =
      Finsupp.single (subgroupRightCoset H g) (A.ρ (subgroupRightPart H g)⁻¹ a) := by
  simp [subgroupInductionTensorCoordinates]

theorem subgroupInductionTensorCoordinates_invariant (h : H) :
    subgroupInductionTensorCoordinates H k A ∘ₗ
      (Representation.tprod ((Representation.leftRegular k G).comp H.subtype) A.ρ) h =
        subgroupInductionTensorCoordinates H k A := by
  apply TensorProduct.ext
  apply MonoidAlgebra.lhom_ext'
  intro g
  apply LinearMap.ext_ring
  apply LinearMap.ext
  intro a
  simp [map_mul, mul_inv_rev, Module.End.mul_apply]

def subgroupInductionCoordinates : Rep.ind H.subtype A →ₗ[k] (subgroupRightCosets H →₀ A) :=
  Coinvariants.lift _ (subgroupInductionTensorCoordinates H k A)
    (subgroupInductionTensorCoordinates_invariant H k A)

@[simp]
theorem subgroupInductionCoordinates_mk (g : G) (a : A) :
    subgroupInductionCoordinates H k A (IndV.mk H.subtype A.ρ g a) =
      Finsupp.single (subgroupRightCoset H g) (A.ρ (subgroupRightPart H g)⁻¹ a) :=
  subgroupInductionTensorCoordinates_single H k A g a

def subgroupInductionCoordinatesInv : (subgroupRightCosets H →₀ A) →ₗ[k] Rep.ind H.subtype A :=
  Finsupp.lsum k fun c => IndV.mk H.subtype A.ρ (subgroupRightRepresentative H c)

@[simp]
theorem subgroupInductionCoordinatesInv_single (c : subgroupRightCosets H) (a : A) :
    subgroupInductionCoordinatesInv H k A (Finsupp.single c a) =
      IndV.mk H.subtype A.ρ (subgroupRightRepresentative H c) a := by
  simp [subgroupInductionCoordinatesInv]

theorem subgroupInductionCoordinates_right_inv :
    (subgroupInductionCoordinates H k A).comp (subgroupInductionCoordinatesInv H k A) =
      LinearMap.id := by
  apply Finsupp.lhom_ext'
  intro c
  apply LinearMap.ext
  intro a
  change subgroupInductionCoordinates H k A
    (subgroupInductionCoordinatesInv H k A (Finsupp.single c a)) = _
  rw [subgroupInductionCoordinatesInv_single, subgroupInductionCoordinates_mk,
    subgroupRightRepresentative_coset, subgroupRightPart_representative]
  simp

theorem subgroupInductionCoordinates_left_inv :
    (subgroupInductionCoordinatesInv H k A).comp (subgroupInductionCoordinates H k A) =
      LinearMap.id := by
  apply IndV.hom_ext
  intro g
  apply LinearMap.ext
  intro a
  change subgroupInductionCoordinatesInv H k A
    (subgroupInductionCoordinates H k A (IndV.mk H.subtype A.ρ g a)) = IndV.mk H.subtype A.ρ g a
  rw [subgroupInductionCoordinates_mk, subgroupInductionCoordinatesInv_single]
  change Coinvariants.mk (Representation.tprod ((Representation.leftRegular k G).comp H.subtype) A.ρ)
    (MonoidAlgebra.single (subgroupRightRepresentative H (subgroupRightCoset H g)) (1 : k) ⊗ₜ[k]
      A.ρ (subgroupRightPart H g)⁻¹ a) =
    Coinvariants.mk (Representation.tprod ((Representation.leftRegular k G).comp H.subtype) A.ρ)
      (MonoidAlgebra.single g (1 : k) ⊗ₜ[k] a)
  rw [Coinvariants.mk_tmul_inv]
  simp only [MonoidHom.comp_apply, Representation.leftRegular, Representation.ofMulAction_single,
    Subgroup.subtype_apply, smul_eq_mul, subgroupRightPart_decompose]

def subgroupInductionEquiv : Rep.ind H.subtype A ≃ₗ[k] (subgroupRightCosets H →₀ A) :=
  LinearEquiv.ofLinearMap (subgroupInductionCoordinates H k A) (subgroupInductionCoordinatesInv H k A)
    (subgroupInductionCoordinates_right_inv H k A) (subgroupInductionCoordinates_left_inv H k A)

end PolycyclicRecognition

end

end OAI
