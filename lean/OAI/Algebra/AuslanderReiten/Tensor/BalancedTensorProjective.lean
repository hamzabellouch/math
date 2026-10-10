import OAI.Algebra.AuslanderReiten.Tensor.BalancedTensorPi
import OAI.Algebra.AuslanderReiten.Tensor.BalancedTensorUnit
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Finiteness.Cardinality

namespace OAI

noncomputable section
namespace ArExplicit.BalancedTensor

private instance finitePiProjective {S P ι : Type*} [Ring S] [AddCommGroup P]
    [Module S P] [Module.Projective S P] [Fintype ι] : Module.Projective S (ι → P) :=
  Module.Projective.of_equiv (DFinsupp.linearEquivFunOnFintype :
    (Π₀ _ : ι, P) ≃ₗ[S] (ι → P))

variable {k R S F M : Type*} [CommRing k] [Ring R] [Ring S] [Algebra k R]
variable [AddCommGroup F] [Module k F] [Module Rᵐᵒᵖ F] [Module S F]
variable [SMulCommClass k S F] [SMulCommClass S Rᵐᵒᵖ F]
variable [IsScalarTower k Rᵐᵒᵖ F]
variable [AddCommGroup M] [Module k M] [Module R M] [IsScalarTower k R M]

theorem projective [Module.Projective S F] [Module.Finite R M] [Module.Projective R M] :
    Module.Projective S (BalancedTensor k R F M) := by
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' R M
  obtain ⟨s, hs⟩ := Module.projective_lifting_property p (LinearMap.id : M →ₗ[R] M) hp
  let : Module.Projective S (BalancedTensor k R F R) :=
    Module.Projective.of_equiv (runitLeft (k := k) (R := R) (S := S) (F := F)).symm
  let : Module.Projective S (BalancedTensor k R F (Fin n → R)) :=
    Module.Projective.of_equiv (piRight (k := k) (R := R) (S := S) (F := F) (M := R)).symm
  apply Module.Projective.of_split (mapRight (k := k) (S := S) s) (mapRight (k := k) (S := S) p)
  rw [← mapRight_comp, hs, mapRight_id]

theorem finite [Module.Finite S F] [Module.Finite R M] :
    Module.Finite S (BalancedTensor k R F M) := by
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' R M
  let : Module.Finite S (BalancedTensor k R F R) :=
    Module.Finite.equiv (runitLeft (k := k) (R := R) (S := S) (F := F)).symm
  let : Module.Finite S (BalancedTensor k R F (Fin n → R)) :=
    Module.Finite.equiv (piRight (k := k) (R := R) (S := S) (F := F) (M := R)).symm
  exact Module.Finite.of_surjective (mapRight (k := k) (S := S) p) (mapRight_surjective p hp)

end ArExplicit.BalancedTensor

end

end OAI
