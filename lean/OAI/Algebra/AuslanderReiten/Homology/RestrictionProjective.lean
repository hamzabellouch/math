import OAI.Algebra.AuslanderReiten.Homology.RestrictKernelCokernel

namespace OAI

noncomputable section

namespace ArExplicit

open CategoryTheory

universe u

variable {R S : Type u} [Ring R] [Ring S] (j : R →+* S)

private instance finitePiProjective {P ι : Type*} [AddCommGroup P] [Module R P]
    [Module.Projective R P] [Fintype ι] : Module.Projective R (ι → P) :=
  Module.Projective.of_equiv (DFinsupp.linearEquivFunOnFintype :
    (Π₀ _ : ι, P) ≃ₗ[R] (ι → P))

def restrictPiEquiv (ι : Type) :
    ((ModuleCat.restrictScalars j).obj (ModuleCat.of S (ι → S))) ≃ₗ[R]
      (ι → ((ModuleCat.restrictScalars j).obj (ModuleCat.of S S))) where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (M : ModuleCat.{u} S) [Module.Finite S M]

theorem restrict_finite [Module.Finite R ((ModuleCat.restrictScalars j).obj (ModuleCat.of S S))] :
    Module.Finite R ((ModuleCat.restrictScalars j).obj M) := by
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' S M
  have : Module.Finite R ((ModuleCat.restrictScalars j).obj (ModuleCat.of S (Fin n → S))) :=
    Module.Finite.equiv (restrictPiEquiv j (Fin n)).symm
  exact Module.Finite.of_surjective
    (((ModuleCat.restrictScalars j).map (ModuleCat.ofHom p)).hom) hp

theorem restrict_projective [Module.Projective S M]
    [Module.Projective R ((ModuleCat.restrictScalars j).obj (ModuleCat.of S S))] :
    Module.Projective R ((ModuleCat.restrictScalars j).obj M) := by
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' S M
  obtain ⟨s, hs⟩ := Module.projective_lifting_property p (LinearMap.id : M →ₗ[S] M) hp
  have : Module.Projective R ((ModuleCat.restrictScalars j).obj (ModuleCat.of S (Fin n → S))) :=
    Module.Projective.of_equiv (restrictPiEquiv j (Fin n)).symm
  apply Module.Projective.of_split
    (((ModuleCat.restrictScalars j).map (ModuleCat.ofHom s)).hom)
    (((ModuleCat.restrictScalars j).map (ModuleCat.ofHom p)).hom)
  apply LinearMap.ext
  intro x
  exact DFunLike.congr_fun hs x

end ArExplicit

end

end OAI
