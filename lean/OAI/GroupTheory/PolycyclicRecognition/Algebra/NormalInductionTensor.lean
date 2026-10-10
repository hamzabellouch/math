import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteIndexTraceRetract
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NormalQuotientCoordinates

namespace OAI

/-! # Induced restriction as the quotient regular representation tensored with a coefficient -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory Representation MonoidalCategory
open scoped MonoidAlgebra TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] TensorProduct.instModule
variable {G : Type} [Group G] (N : Subgroup G) [N.Normal] (A : Rep.{0} ℤ G)

abbrev quotientRegularTensor : Rep ℤ G :=
  Rep.res (QuotientGroup.mk' N) (Rep.leftRegular ℤ (G ⧸ N)) ⊗ A

def normalInductionTensorRaw : ℤ[G] ⊗[ℤ] A →ₗ[ℤ] quotientRegularTensor N A :=
  TensorProduct.lift <|
    (Finsupp.lift _ _ _ fun g =>
      (TensorProduct.mk ℤ _ _ (MonoidAlgebra.single (QuotientGroup.mk' N g⁻¹) (1 : ℤ))).comp
        (A.ρ g⁻¹)) ∘ₗ (MonoidAlgebra.coeffLinearEquiv ℤ).toLinearMap

@[simp]
theorem normalInductionTensorRaw_single (g : G) (a : A) :
    normalInductionTensorRaw N A (MonoidAlgebra.single g 1 ⊗ₜ[ℤ] a) =
      MonoidAlgebra.single (QuotientGroup.mk' N g⁻¹) (1 : ℤ) ⊗ₜ[ℤ] A.ρ g⁻¹ a := by
  simp [normalInductionTensorRaw]

theorem normalInductionTensorRaw_invariant (n : N) :
    (normalInductionTensorRaw N A).comp
      ((Representation.tprod ((Representation.leftRegular ℤ G).comp N.subtype)
        (A.ρ.comp N.subtype)) n) = normalInductionTensorRaw N A := by
  apply TensorProduct.ext
  apply MonoidAlgebra.lhom_ext'
  intro g
  apply LinearMap.ext_ring
  ext a
  simp [normalInductionTensorRaw, mul_inv_rev, map_mul, Module.End.mul_apply]
  have hn : (QuotientGroup.mk' N) (n : G) = 1 := normalQuotient_mk_subgroup N n
  change MonoidAlgebra.single ((QuotientGroup.mk' N g)⁻¹ *
    (QuotientGroup.mk' N (n : G))⁻¹) (1 : ℤ) ⊗ₜ[ℤ] A.ρ g⁻¹ a = _
  rw [hn, inv_one, mul_one]
  rfl

def normalInductionTensorLinear :
    Rep.ind N.subtype (Rep.res N.subtype A) →ₗ[ℤ] quotientRegularTensor N A :=
  Coinvariants.lift _ (normalInductionTensorRaw N A) (normalInductionTensorRaw_invariant N A)

@[simp]
theorem normalInductionTensorLinear_mk (g : G) (a : A) :
    normalInductionTensorLinear N A (IndV.mk _ _ g a) =
      MonoidAlgebra.single (QuotientGroup.mk' N g⁻¹) (1 : ℤ) ⊗ₜ[ℤ] A.ρ g⁻¹ a :=
  normalInductionTensorRaw_single N A g a

def normalInductionTensorHom :
    Rep.ind N.subtype (Rep.res N.subtype A) ⟶ quotientRegularTensor N A :=
  Rep.ofHom ⟨normalInductionTensorLinear N A, fun g => by
    apply IndV.hom_ext
    intro h
    ext a
    change normalInductionTensorLinear N A ((Representation.ind _ _) g (IndV.mk _ _ h a)) =
      (quotientRegularTensor N A).ρ g (normalInductionTensorLinear N A (IndV.mk _ _ h a))
    rw [ind_mk, normalInductionTensorLinear_mk, normalInductionTensorLinear_mk]
    simp [quotientRegularTensor, mul_inv_rev, map_mul, Module.End.mul_apply]⟩

def normalTensorTerm (g : G) : A →ₗ[ℤ] Rep.ind N.subtype (Rep.res N.subtype A) :=
  (IndV.mk N.subtype (Rep.res N.subtype A).ρ g⁻¹).comp (A.ρ g⁻¹)

theorem normalTensorTerm_eq (g h : G)
    (hgh : QuotientGroup.mk' N g = QuotientGroup.mk' N h) :
    normalTensorTerm N A g = normalTensorTerm N A h := by
  let n : N := ⟨h⁻¹ * g, by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' N (h⁻¹ * g) = 1
    rw [map_mul, map_inv, hgh, inv_mul_cancel]⟩
  have hn : h⁻¹ = (n : G) * g⁻¹ := by simp [n, mul_assoc]
  ext a
  change IndV.mk _ _ g⁻¹ (A.ρ g⁻¹ a) = IndV.mk _ _ h⁻¹ (A.ρ h⁻¹ a)
  rw [hn, map_mul, Module.End.mul_apply]
  exact (induced_mk_mul_left N (Rep.res N.subtype A) n g⁻¹ (A.ρ g⁻¹ a)).symm

def normalTensorQuotientTerm (c : G ⧸ N) :
    A →ₗ[ℤ] Rep.ind N.subtype (Rep.res N.subtype A) :=
  normalTensorTerm N A (normalQuotientRepresentative N c)

@[simp]
theorem normalTensorQuotientTerm_mk (g : G) :
    normalTensorQuotientTerm N A (QuotientGroup.mk' N g) = normalTensorTerm N A g :=
  normalTensorTerm_eq N A _ _ (normalQuotientRepresentative_mk N _)

def normalInductionTensorInvLinear :
    quotientRegularTensor N A →ₗ[ℤ] Rep.ind N.subtype (Rep.res N.subtype A) :=
  TensorProduct.lift <|
    (Finsupp.lift _ _ _ (normalTensorQuotientTerm N A)) ∘ₗ
      (MonoidAlgebra.coeffLinearEquiv ℤ).toLinearMap

@[simp]
theorem normalInductionTensorInvLinear_single (g : G) (a : A) :
    normalInductionTensorInvLinear N A
      (MonoidAlgebra.single (QuotientGroup.mk' N g) 1 ⊗ₜ[ℤ] a) =
        IndV.mk _ _ g⁻¹ (A.ρ g⁻¹ a) := by
  have h : normalInductionTensorInvLinear N A
      (MonoidAlgebra.single (QuotientGroup.mk' N g) (1 : ℤ) ⊗ₜ[ℤ] a) =
      normalTensorQuotientTerm N A (QuotientGroup.mk' N g) a := by
    simp [normalInductionTensorInvLinear]
  rw [h, normalTensorQuotientTerm_mk]
  rfl

theorem normalInductionTensor_left_inv :
    (normalInductionTensorInvLinear N A).comp (normalInductionTensorLinear N A) =
      LinearMap.id := by
  apply IndV.hom_ext
  intro g
  ext a
  change normalInductionTensorInvLinear N A
    (normalInductionTensorLinear N A (IndV.mk _ _ g a)) = IndV.mk _ _ g a
  rw [normalInductionTensorLinear_mk, normalInductionTensorInvLinear_single]
  simp [← Module.End.mul_apply, ← map_mul]

theorem normalInductionTensor_right_inv :
    (normalInductionTensorLinear N A).comp (normalInductionTensorInvLinear N A) =
      LinearMap.id := by
  apply TensorProduct.ext
  apply MonoidAlgebra.lhom_ext'
  intro c
  apply LinearMap.ext_ring
  ext a
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N c
  change normalInductionTensorLinear N A (normalInductionTensorInvLinear N A
    (MonoidAlgebra.single (QuotientGroup.mk' N g) (1 : ℤ) ⊗ₜ[ℤ] a)) = _
  rw [normalInductionTensorInvLinear_single, normalInductionTensorLinear_mk]
  simp [← Module.End.mul_apply, ← map_mul]

def normalInductionTensorEquiv :
    Rep.ind N.subtype (Rep.res N.subtype A) ≃ₗ[ℤ] quotientRegularTensor N A :=
  LinearEquiv.ofLinearMap (normalInductionTensorLinear N A) (normalInductionTensorInvLinear N A)
    (normalInductionTensor_right_inv N A) (normalInductionTensor_left_inv N A)

/-- This is an isomorphism of the actual ambient group representations. -/
def normalInductionTensorIso :
    Rep.ind N.subtype (Rep.res N.subtype A) ≅ quotientRegularTensor N A :=
  by
    let f := normalInductionTensorHom N A
    let : Mono f := (Rep.mono_iff_injective f).mpr (normalInductionTensorEquiv N A).injective
    let : Epi f := (Rep.epi_iff_surjective f).mpr (normalInductionTensorEquiv N A).surjective
    let : IsIso f := isIso_of_mono_of_epi f
    exact asIso f

end PolycyclicRecognition

end

end OAI
