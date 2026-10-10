import OAI.GroupTheory.PolycyclicRecognition.Analysis.TrivialTensorChains

namespace OAI

/-! # Naturality of the trivial-coefficient tensor comparison -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory MonoidalCategory
open scoped TensorProduct
attribute [local instance 2000] Rep.hV2
variable {k G H : Type} [CommRing k] [Group G] [Group H]
  {V W : ModuleCat k} {A : Rep k G} {B : Rep k H}

def trivialTensorCoefficientMap (u : V ⟶ W) (f : G →* H) (φ : A ⟶ Rep.res f B) :
    trivialTensorCoefficient V A ⟶ Rep.res f (trivialTensorCoefficient W B) :=
  Rep.ofHom ⟨TensorProduct.map u.hom φ.hom.toLinearMap, by
    intro g
    apply TensorProduct.ext
    apply LinearMap.ext
    intro v
    apply LinearMap.ext
    intro a
    change u.hom v ⊗ₜ[k] φ.hom (A.ρ g a) = u.hom v ⊗ₜ[k] B.ρ (f g) (φ.hom a)
    rw [Rep.hom_comm_apply]
    rfl⟩

theorem trivialTensorChainsIso_naturality [DecidableEq G] [DecidableEq H]
    (u : V ⟶ W) (f : G →* H) (φ : A ⟶ Rep.res f B) :
    (trivialTensorChainsIso V A).hom ≫
        groupHomology.chainsMap f (trivialTensorCoefficientMap u f φ) =
      (((tensorLeft V).mapHomologicalComplex (ComplexShape.down ℕ)).map
        (groupHomology.chainsMap f φ)) ≫
        (NatTrans.mapHomologicalComplex ((curriedTensor (ModuleCat k)).map u) (ComplexShape.down ℕ)).app
          (groupHomology.inhomogeneousChains B) ≫
        (trivialTensorChainsIso W B).hom := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  apply LinearMap.ext
  intro v
  apply Finsupp.lhom_ext'
  intro x
  apply LinearMap.ext
  intro a
  change (groupHomology.chainsMap f (trivialTensorCoefficientMap u f φ)).f i
      (TensorProduct.finsuppRight k k V A.V (Fin i → G) (v ⊗ₜ[k] Finsupp.single x a)) =
    TensorProduct.finsuppRight k k W B.V (Fin i → H)
      (u.hom v ⊗ₜ[k] (groupHomology.chainsMap f φ).f i (Finsupp.single x a))
  erw [TensorProduct.finsuppRight_tmul_single, groupHomology.chainsMap_f_single,
    groupHomology.chainsMap_f_single, TensorProduct.finsuppRight_tmul_single]
  rfl

end PolycyclicRecognition

end

end OAI
