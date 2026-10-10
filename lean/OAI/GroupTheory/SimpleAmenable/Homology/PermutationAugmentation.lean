import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.FullGroupStability

namespace OAI

open Classical CategoryTheory CategoryTheory.Limits Representation Rep Finsupp
namespace SimpleAmenable.TransitiveInduction

attribute [local instance 1200] Rep.hV2
variable {G X Y : Type} [Group G] [MulAction G X] [MulAction G Y]

noncomputable def augmentation (G X : Type) [Group G] [MulAction G X] :
    Rep.of (permutationRep (G:=G) (X:=X)) ⟶ Rep.trivial ℤ G ℤ :=
  Rep.ofHom ⟨Finsupp.lsum ℤ (fun _ => (LinearMap.id : ℤ →ₗ[ℤ] ℤ)), by
    intro g
    apply Finsupp.lhom_ext
    intro x z
    change (Finsupp.lsum ℤ (fun _ : X => (LinearMap.id : ℤ →ₗ[ℤ] ℤ)))
      (permutationRep (G:=G) (X:=X) g (single x z))=
      (Finsupp.lsum ℤ (fun _ : X => (LinearMap.id : ℤ →ₗ[ℤ] ℤ))) (single x z)
    rw [permutationRep_single]
    simp⟩

@[simp] lemma augmentation_single (x : X) (z : ℤ) :
    (augmentation G X).hom (single x z)=z := by simp [augmentation]

lemma augmentation_natural (f : X → Y) (hf : ∀g : G,∀x,f (g • x)=g • f x) :
    equivariantMap f hf ≫ augmentation G Y=augmentation G X := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply Finsupp.lhom_ext
  intro x z
  change (augmentation G Y).hom ((equivariantMap f hf).hom (single x z))=
    (augmentation G X).hom (single x z)
  rw [equivariantMap_single, augmentation_single, augmentation_single]
lemma augmentation_pointMap (x : X) (q : ℕ) :
    groupHomology.map (MulAction.stabilizer G x).subtype (pointMap x) q ≫
      (groupHomology.functor ℤ G q).map (augmentation G X) =
    TrivialHomology.map (MulAction.stabilizer G x).subtype q := by
  erw [groupHomology.functor_map, ← groupHomology.map_comp]
  apply groupHomology.map_congr
  · rfl
  · apply LinearMap.ext
    intro z
    change (augmentation G X).hom (single x z)=z
    exact augmentation_single x z
lemma isIso_H0_augmentation (x : X) (ht : ∀y:X,∃g:G,g • x=y) :
    IsIso ((groupHomology.functor ℤ G 0).map (augmentation G X)) := by
  have pointIso := isIso_map_pointMap x ht 0
  have trivialIso := isIso_map_trivial_H0 (MulAction.stabilizer G x).subtype
  exact @IsIso.of_isIso_fac_left _ _ _ _ _ _ _ _ pointIso trivialIso
    (augmentation_pointMap x 0)

lemma map_equivariant_H0_eq (f₀ f₁ : X → Y)
    (h₀ : ∀g : G,∀x,f₀ (g • x)=g • f₀ x)
    (h₁ : ∀g : G,∀x,f₁ (g • x)=g • f₁ x)
    (y : Y) (ht : ∀z:Y,∃g:G,g • y=z) :
    (groupHomology.functor ℤ G 0).map (equivariantMap f₀ h₀)=
      (groupHomology.functor ℤ G 0).map (equivariantMap f₁ h₁) := by
  have := isIso_H0_augmentation y ht
  apply (cancel_mono ((groupHomology.functor ℤ G 0).map (augmentation G Y))).1
  rw [← Functor.map_comp, ← Functor.map_comp, augmentation_natural, augmentation_natural]
end SimpleAmenable.TransitiveInduction

end OAI
