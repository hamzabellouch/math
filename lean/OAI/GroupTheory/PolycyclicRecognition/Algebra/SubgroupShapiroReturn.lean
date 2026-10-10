import OAI.GroupTheory.PolycyclicRecognition.Algebra.SubgroupShapiro

namespace OAI

/-! # Subgroup inclusion is the Shapiro coefficient return -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory HomologicalComplex
variable {G : Type} [Group G]

theorem subgroupShapiro_return (H : Subgroup G) (A : Rep ℤ G) (n : ℕ) :
    (subgroupShapiroIso H (Rep.res H.subtype A) n).hom ≫
      groupHomology.map (MonoidHom.id G) (finiteIndexReturn H A) n =
        subgroupHomologyInclusion H A n := by
  classical
  let Q : ProjectiveResolution (Rep.trivial ℤ H ℤ) :=
    (Rep.resFunctor H.subtype).mapProjectiveResolution (Rep.barResolution ℤ G)
  let u : Rep.barComplex ℤ H ⟶ Q.complex := subgroupBarResolutionMap H
  let F := (Rep.coinvariantsTensor ℤ H).obj (Rep.res H.subtype A)
  let s : Q.complex.coinvariantsTensorObj (Rep.res H.subtype A) ≅
      (Rep.barComplex ℤ G).coinvariantsTensorObj (Rep.ind H.subtype (Rep.res H.subtype A)) :=
    groupHomology.coinvariantsTensorResProjectiveResolutionIso H
      (Rep.res H.subtype A) (Rep.barResolution ℤ G)
  let a := groupHomology.inhomogeneousChainsIso (Rep.res H.subtype A)
  let b := groupHomology.inhomogeneousChainsIso (Rep.ind H.subtype (Rep.res H.subtype A))
  let e := groupHomology.inhomogeneousChainsIso A
  apply (cancel_mono (homologyMap e.hom n)).mp
  have hn := congrArg (fun f => homologyMap f n)
    (inhomogeneousChainsIso_coefficient (finiteIndexReturn H A))
  simp only [homologyMap_comp] at hn
  have hc := congrArg (fun f => homologyMap f n) (subgroupShapiro_return_chain H A)
  change homologyMap (a.hom ≫ (F.mapHomologicalComplex _).map u ≫ s.hom ≫
    coefficientTensorChainMap (Rep.barComplex ℤ G) (finiteIndexReturn H A)) n =
      homologyMap (subgroupBarInclusion H A ≫ e.hom) n at hc
  simp only [homologyMap_comp] at hc
  change (((coefficientNaturalHomologyIso Q (Rep.res H.subtype A) n).hom ≫
      homologyMap s.hom n) ≫ homologyMap b.inv n) ≫
      homologyMap (groupHomology.chainsMap (MonoidHom.id G) (finiteIndexReturn H A)) n ≫
      homologyMap e.hom n = homologyMap (subgroupBarInclusion H A) n ≫ homologyMap e.hom n
  rw [subgroup_comparison_homology]
  simp only [Category.assoc]
  rw [hn]
  have hb : homologyMap b.inv n ≫ homologyMap b.hom n = 𝟙 _ := by
    rw [← homologyMap_comp, b.inv_hom_id, homologyMap_id]
  erw [← Category.assoc (homologyMap b.inv n), hb, Category.id_comp]
  exact hc

end PolycyclicRecognition

end

end OAI
