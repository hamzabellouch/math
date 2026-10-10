import OAI.GroupTheory.PolycyclicRecognition.Finiteness.NormalHomologyActionComparison

namespace OAI

/-! # FP-infinity gives finite subgroup homology with its conjugation action -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
open scoped IsMulCommutative
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G] (N : Subgroup G) [N.Normal]

omit [N.Normal] in
theorem normalSubgroupBarChains_homology_isIso [DecidableEq N] (i : ℕ) :
    IsIso (HomologicalComplex.homologyMap (normalSubgroupBarChains N) i) := by
  let F := Rep.coinvariantsFunctor ℤ N
  let E := ProjectiveResolution.homotopyEquiv (Rep.barResolution ℤ N)
    ((Rep.resFunctor.{0} N.subtype).mapProjectiveResolution (Rep.barResolution ℤ G))
  have he := (F.mapHomotopy (subgroupBarResolutionHomotopy N)).homologyMap_eq i
  have hi : IsIso (HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map (subgroupBarResolutionMap N)) i) := by
    rw [he]
    exact ((F.mapHomotopyEquiv E).toHomologyIso i).isIso_hom
  let := hi
  change IsIso (HomologicalComplex.homologyMap
    ((trivialBarCoinvariantsIso N).hom ≫
      (F.mapHomologicalComplex (ComplexShape.down ℕ)).map (subgroupBarResolutionMap N)) i)
  rw [HomologicalComplex.homologyMap_comp]
  infer_instance

def normalSubgroupHomologyUnderlyingIso [DecidableEq N] (i : ℕ) :
    groupHomology (Rep.trivial ℤ N ℤ) i ≅
      (forget₂ (Rep.{0} ℤ (G ⧸ N)) (ModuleCat ℤ)).obj ((normalBarComplex N).homology i) := by
  let f := HomologicalComplex.homologyMap (normalSubgroupBarChains N) i
  let : IsIso f :=
    normalSubgroupBarChains_homology_isIso N i
  let e := asIso f
  exact e ≪≫
    ((normalBarComplex N).sc i).mapHomologyIso (forget₂ (Rep.{0} ℤ (G ⧸ N)) (ModuleCat ℤ))

theorem normalSubgroupHomologyUnderlyingIso_equivariant [DecidableEq N] (g : G) (i : ℕ) :
    normalHomologyMap ℤ N (trivialIntegral G) i g ≫
        (normalSubgroupHomologyUnderlyingIso N i).hom =
      (normalSubgroupHomologyUnderlyingIso N i).hom ≫
        ModuleCat.ofHom (((normalBarComplex N).homology i).ρ (QuotientGroup.mk' N g)) := by
  let e := ((normalBarComplex N).sc i).mapHomologyIso
    (forget₂ (Rep.{0} ℤ (G ⧸ N)) (ModuleCat ℤ))
  let f : groupHomology (Rep.res N.subtype (trivialIntegral G)) i ⟶ _ :=
    HomologicalComplex.homologyMap (normalSubgroupBarChains N) i
  change normalHomologyMap ℤ N (trivialIntegral G) i g ≫ (f ≫ e.hom) =
    (f ≫ e.hom) ≫ _
  have hm := underlyingHomologyAction (normalBarComplex N) (QuotientGroup.mk' N g) i
  have hn := normalSubgroupBarHomology_conjugation N g i
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ e.hom) hn).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun k => f ≫ k) ((Iso.inv_comp_eq e).mp hm.symm)).trans
          (Category.assoc _ _ _).symm)))

def normalSubgroupHomologyIso [DecidableEq N] (i : ℕ) :
    quotientHomologyAction N (trivialIntegral G) i ≅ (normalBarComplex N).homology i := by
  let e := normalSubgroupHomologyUnderlyingIso N i
  refine Rep.mkIso (Representation.Equiv.mk e.toLinearEquiv ?_)
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
  apply LinearMap.ext
  intro x
  exact congrArg (fun f => f.hom x) (normalSubgroupHomologyUnderlyingIso_equivariant N g i)

theorem typeFPInfinity_normalHomologyQuotient_finite [Group.FG G]
    [IsMulCommutative (G ⧸ N)] (h : TypeFPInfinity G) (i : ℕ) :
    IntegralRepresentationFinite (G ⧸ N) (quotientHomologyAction N (trivialIntegral G) i) := by
  classical
  have hd := typeFPInfinity_normalDerivedHomology_finite N h i
  have hb : IntegralRepresentationFinite (G ⧸ N) ((normalBarComplex N).homology i) :=
    hd.of_iso ((Rep.barResolution ℤ G).isoLeftDerivedObj
      (Rep.quotientToCoinvariantsFunctor.{0} ℤ N) i)
  exact hb.of_iso (normalSubgroupHomologyIso N i).symm

end PolycyclicRecognition

end

end OAI
