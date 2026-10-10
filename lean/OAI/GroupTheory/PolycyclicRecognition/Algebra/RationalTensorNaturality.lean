import OAI.GroupTheory.PolycyclicRecognition.Finiteness.RationalTensorHomology
import OAI.GroupTheory.PolycyclicRecognition.Analysis.TrivialTensorChainNaturality

namespace OAI

/-! # Naturality of rational coefficient homology -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory MonoidalCategory
attribute [local instance 2000] Rep.hV2

theorem rationalChainHomologyIso_tensorMap (C : ChainComplex (ModuleCat ℤ) ℕ)
    (u : ModuleCat.of ℤ ℚ ⟶ ModuleCat.of ℤ ℚ) (n : ℕ) :
    HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex ((curriedTensor (ModuleCat ℤ)).map u)
          (ComplexShape.down ℕ)).app C) n ≫ (rationalChainHomologyIso C n).hom =
      (rationalChainHomologyIso C n).hom ≫
        (((curriedTensor (ModuleCat ℤ)).map u).app (C.homology n)) := by
  have h := NatTrans.app_homology ((curriedTensor (ModuleCat ℤ)).map u) (C.sc n)
  change ((curriedTensor (ModuleCat ℤ)).map u).app (C.homology n) =
    (rationalChainHomologyIso C n).inv ≫
      HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex ((curriedTensor (ModuleCat ℤ)).map u)
          (ComplexShape.down ℕ)).app C) n ≫ (rationalChainHomologyIso C n).hom at h
  rw [h]
  simp only [Iso.hom_inv_id_assoc]

theorem rationalTensorHomologyIso_naturality {G H : Type} [Group G] [Group H]
    [DecidableEq G] [DecidableEq H] (A : Rep ℤ G) (B : Rep ℤ H)
    (u : ModuleCat.of ℤ ℚ ⟶ ModuleCat.of ℤ ℚ) (f : G →* H)
    (φ : A ⟶ Rep.res f B) (n : ℕ) :
    groupHomology.map f (trivialTensorCoefficientMap u f φ) n ≫
        (rationalTensorHomologyIso B n).hom =
      (rationalTensorHomologyIso A n).hom ≫
        (tensorLeft (ModuleCat.of ℤ ℚ)).map (groupHomology.map f φ n) ≫
        (((curriedTensor (ModuleCat ℤ)).map u).app (groupHomology B n)) := by
  let T := (tensorLeft (ModuleCat.of ℤ ℚ)).mapHomologicalComplex (ComplexShape.down ℕ)
  let E := trivialTensorChainsIso (ModuleCat.of ℤ ℚ) A
  let F := trivialTensorChainsIso (ModuleCat.of ℤ ℚ) B
  let c := groupHomology.chainsMap f φ
  let v := (NatTrans.mapHomologicalComplex ((curriedTensor (ModuleCat ℤ)).map u)
    (ComplexShape.down ℕ)).app (groupHomology.inhomogeneousChains B)
  have h := trivialTensorChainsIso_naturality u f φ
  change E.hom ≫ groupHomology.chainsMap f (trivialTensorCoefficientMap u f φ) =
    T.map c ≫ v ≫ F.hom at h
  have hc : groupHomology.chainsMap f (trivialTensorCoefficientMap u f φ) ≫ F.inv =
      E.inv ≫ T.map c ≫ v := by
    rw [← cancel_epi E.hom]
    simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
      Category.comp_id] using congrArg (fun z => z ≫ F.inv) h
  change HomologicalComplex.homologyMap _ n ≫
      (HomologicalComplex.homologyMap F.inv n ≫
        (rationalChainHomologyIso (groupHomology.inhomogeneousChains B) n).hom) = _
  rw [← Category.assoc, ← HomologicalComplex.homologyMap_comp, hc,
    HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp]
  simp only [Category.assoc]
  rw [rationalChainHomologyIso_tensorMap,
    ← Category.assoc (HomologicalComplex.homologyMap (T.map c) n),
    rationalChainHomologyIso_naturality]
  rfl

end PolycyclicRecognition

end

end OAI
