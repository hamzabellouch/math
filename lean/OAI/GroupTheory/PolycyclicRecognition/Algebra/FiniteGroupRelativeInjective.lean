import OAI.GroupTheory.PolycyclicRecognition.Finiteness.FiniteGroupProjectiveNorm

namespace OAI

/-! # Extending maps into projectives across integral split inclusions

For a finite group, a projective representation is injective with respect to
short exact sequences that split as sequences of abelian groups. The extension
uses the coefficient at the identity followed by the finite group sum.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G] [Fintype G]

def freeIdentityCoefficient (α : Type) : Module.End ℤ (Rep.free ℤ G α) :=
  Finsupp.mapRange.linearMap
    (MonoidAlgebra.lsingle 1 ∘ₗ Finsupp.lapply 1 ∘ₗ
      (MonoidAlgebra.coeffLinearEquiv ℤ).toLinearMap)

omit [Fintype G] in
@[simp]
theorem freeIdentityCoefficient_apply (α : Type) (x : Rep.free ℤ G α) (a : α) :
    freeIdentityCoefficient α x a = MonoidAlgebra.single 1 ((x a).coeff 1) := rfl

def freeAveragedLinearMap {α : Type} (B : Rep.{0} ℤ G)
    (l : B →ₗ[ℤ] Rep.free ℤ G α) : B →ₗ[ℤ] Rep.free ℤ G α :=
  ∑ g : G, (Rep.free ℤ G α).ρ g ∘ₗ freeIdentityCoefficient α ∘ₗ l ∘ₗ B.ρ g⁻¹

theorem freeAveragedLinearMap_coeff {α : Type} (B : Rep.{0} ℤ G)
    (l : B →ₗ[ℤ] Rep.free ℤ G α) (b : B) (a : α) (h : G) :
    (freeAveragedLinearMap B l b a).coeff h = (l (B.ρ h⁻¹ b) a).coeff 1 := by
  classical
  calc
    _ = ∑ g : G, (Representation.free ℤ G α g
        (freeIdentityCoefficient α (l (B.ρ g⁻¹ b))) a).coeff h := by
      simp [freeAveragedLinearMap]
    _ = ∑ g : G, (freeIdentityCoefficient α (l (B.ρ g⁻¹ b)) a).coeff (g⁻¹ * h) := by
      apply Finset.sum_congr rfl
      intro g _
      exact freeRepresentation_action_coeff g _ a h
    _ = _ := by simp [freeIdentityCoefficient, MonoidAlgebra.coeff_single, Finsupp.single_apply, eq_comm, inv_mul_eq_one]

def freeAveragedExtension {α : Type} (B : Rep.{0} ℤ G)
    (l : B →ₗ[ℤ] Rep.free ℤ G α) : B ⟶ Rep.free ℤ G α :=
  Rep.ofHom ⟨freeAveragedLinearMap B l, fun g => by
    apply LinearMap.ext
    intro b
    ext a h
    change (freeAveragedLinearMap B l (B.ρ g b) a).coeff h =
      (Representation.free ℤ G α g (freeAveragedLinearMap B l b) a).coeff h
    rw [freeAveragedLinearMap_coeff, freeRepresentation_action_coeff,
      freeAveragedLinearMap_coeff]
    congr 2
    simp only [mul_inv_rev, inv_inv, map_mul, Module.End.mul_apply]⟩

theorem freeAveragedExtension_eq {α : Type} {A B : Rep.{0} ℤ G}
    (i : A ⟶ B) (f : A ⟶ Rep.free ℤ G α)
    (l : B →ₗ[ℤ] Rep.free ℤ G α) (hl : ∀ a, l (i.hom a) = f.hom a) :
    i ≫ freeAveragedExtension B l = f := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  ext a h
  change (freeAveragedLinearMap B l (i.hom x) a).coeff h = (f.hom x a).coeff h
  rw [freeAveragedLinearMap_coeff, ← Rep.hom_comm_apply, hl, Rep.hom_comm_apply]
  change (Representation.free ℤ G α h⁻¹ (f.hom x) a).coeff 1 = _
  rw [freeRepresentation_action_coeff]
  simp

theorem projective_extend_of_integral_retraction {A B : Rep.{0} ℤ G}
    (i : A ⟶ B) (r : B →ₗ[ℤ] A) (hr : ∀ a, r (i.hom a) = a)
    (P : Rep.{0} ℤ G) [Projective P] (f : A ⟶ P) :
    ∃ F : B ⟶ P, i ≫ F = f := by
  let s := Projective.factorThru (𝟙 P) (normalizedFreeAugmentation P)
  have hs : s ≫ normalizedFreeAugmentation P = 𝟙 P := Projective.factorThru_comp _ _
  let l : B →ₗ[ℤ] normalizedFreeRepresentation P := (f ≫ s).hom.toLinearMap ∘ₗ r
  let F := freeAveragedExtension B l
  have he : i ≫ F = f ≫ s := by
    apply freeAveragedExtension_eq
    intro a
    change (f ≫ s).hom (r (i.hom a)) = (f ≫ s).hom a
    rw [hr]
  refine ⟨F ≫ normalizedFreeAugmentation P, ?_⟩
  erw [← Category.assoc, he, Category.assoc, hs, Category.comp_id]

end PolycyclicRecognition

end

end OAI
