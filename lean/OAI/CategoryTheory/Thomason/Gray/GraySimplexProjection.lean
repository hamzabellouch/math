import OAI.CategoryTheory.Thomason.Gray.GrayMappingEndpointEvaluation
import OAI.CategoryTheory.Thomason.Gray.TopologicalConePrism
import OAI.CategoryTheory.Thomason.Simplicial.SingularPathSpaceAdjunction

namespace OAI

section

/-! # Actual realization equivalences on the finite Gray parameters

The constructed global collapse restricts to the literal weak chain
collapse on every globe and binary pasting. Both surrounding comparison
maps are proved strict isomorphisms.
-/

namespace Thomason.Construction.StrictOmegaCategory.GrayChainExtension

open CategoryTheory _root_.OAI.Thomason.Construction.DirectedComplex

noncomputable section

theorem projection_parameter (i : GlobePasting.Shape) :
    projection.app (GlobePasting.object i) =
      parameterIso.inv.app i ≫ parameterProjection.app i := by
  let C := GlobePasting.object i
  let e : model.obj C ≅ cylinder.obj C := parameterIso.app i
  let p : model.obj C ⟶ C := parameterProjection.app i
  have hp : e.hom ≫ projection.app C = p :=
    congrArg (fun t => t.app i) projection_parameters
  change projection.app C = e.inv ≫ p
  exact (e.inv_hom_id_assoc (projection.app C)).symm.trans
    (congrArg (fun f => e.inv ≫ f) hp)

/-- The constructed collapse is an actual Street-realization weak
equivalence on every finite parameter used by its extension. -/
theorem projection_parameter_weak (h : NormalizedSimplexIdentities)
    (i : GlobePasting.Shape) :
    h.streetWeakEquivalences (projection.app (GlobePasting.object i)) := by
  have : h.streetWeakEquivalences.HasTwoOutOfThreeProperty :=
    inferInstanceAs (realizationWeakEquivalences.inverseImage h.streetNerve).HasTwoOutOfThreeProperty
  have : h.streetWeakEquivalences.ContainsIdentities :=
    inferInstanceAs (realizationWeakEquivalences.inverseImage h.streetNerve).ContainsIdentities
  have : h.streetWeakEquivalences.RespectsIso :=
    inferInstanceAs (realizationWeakEquivalences.inverseImage h.streetNerve).RespectsIso
  let C := GlobePasting.object i
  let e : model.obj C ≅ cylinder.obj C := parameterIso.app i
  let u : C ≅ (Abelianization.complex C).realization := parameterUnitIso.app i
  let q : model.obj C ⟶ (Abelianization.complex C).realization := modelCollapse.app C
  have hp : projection.app C = e.inv ≫ (q ≫ u.inv) := projection_parameter i
  have he : h.streetWeakEquivalences e.inv :=
    MorphismProperty.of_isIso h.streetWeakEquivalences e.inv
  have hu : h.streetWeakEquivalences u.inv :=
    MorphismProperty.of_isIso h.streetWeakEquivalences u.inv
  have hq : h.streetWeakEquivalences q :=
    h.chainCylinder_projection_weak (Abelianization.complex C)
  have hw : h.streetWeakEquivalences (e.inv ≫ (q ≫ u.inv)) :=
    h.streetWeakEquivalences.comp_mem _ _ he
      (h.streetWeakEquivalences.comp_mem _ _ hq hu)
  exact hp.symm ▸ hw

end
end Thomason.Construction.StrictOmegaCategory.GrayChainExtension

end

section

/-! # Exact agreement of the extended cylinder with ordered chain cylinders -/

namespace Thomason.Construction.StrictOmegaCategory.GrayChainExtension

open CategoryTheory _root_.OAI.Thomason.Construction.DirectedComplex

noncomputable section

/-- The actual extended cylinder agrees with the positive chain cylinder on
every ordered atomic realization whose cylinder basis has the proved order. -/
def orderedRealizationCylinderIso {K : DirectedComplex.{0}} (B : OrderedAtomBasis K)
    (hs : B.SideHeight) : cylinder.obj K.realization ≅ (rightCylinder K).realization :=
  (B.cylinderOrderedAtomBasis hs).comparisonIso (cylinderAtomLift B) (comparisonToRealization K)
    (fun a => atomLift_image B a.2) (fun a => atomLift_dimension B a.2)
      (generated_from_atoms B)

@[simp] theorem orderedRealizationCylinderIso_hom {K : DirectedComplex.{0}}
    (B : OrderedAtomBasis K) (hs : B.SideHeight) :
    (orderedRealizationCylinderIso B hs).hom = comparisonToRealization K := rfl

theorem comparisonToRealization_isIso {K : DirectedComplex.{0}}
    (B : OrderedAtomBasis K) (hs : B.SideHeight) : IsIso (comparisonToRealization K) := by
  change IsIso (orderedRealizationCylinderIso B hs).hom
  infer_instance

/-- In particular, the actual cylinder of each oriental is its literal
normalized-chain right cylinder. -/
def simplexCylinderIso (h : NormalizedSimplexIdentities) (m : ℕ) :
    cylinder.obj (h.object m) ≅
      (rightCylinder (SimplexComplex.directedComplex m (h.squared m))).realization :=
  orderedRealizationCylinderIso (SimplexComplex.orderedAtomBasis h m)
    (SimplexComplex.orderedAtomBasis_sideHeight h m)

end
end Thomason.Construction.StrictOmegaCategory.GrayChainExtension

end

section

/-! # Compatibility of the actual simplex cylinder collapse

The oriental abelianization unit is invertible. The natural chain-cylinder
comparison intertwines collapse before and after the global extension.
-/

namespace Thomason.Construction.NormalizedSimplexIdentities

open CategoryTheory _root_.OAI.Thomason.Construction.DirectedComplex

noncomputable section

variable (h : NormalizedSimplexIdentities)

/-- On an actual oriental, the abelianization unit is a strict isomorphism. -/
def orientalUnitIso (m : ℕ) :
    h.object m ≅ (StrictOmegaCategory.Abelianization.complex (h.object m)).realization :=
  realizationFunctor.mapIso ((simplexAtoms h).abelianizationIso m).symm

theorem orientalUnitIso_hom (m : ℕ) :
    (h.orientalUnitIso m).hom = StrictOmegaCategory.Abelianization.unit (h.object m) :=
  ((simplexAtoms h).unit_eq_realized_inverse m).symm

/-- The concrete chain comparison commutes with interval collapse. -/
theorem constructedChainModelComparison_projection (m : SimplexCategory) :
    h.constructedChainModelComparison.hom.app m ≫
        StrictOmegaCategory.GrayChainExtension.modelCollapse.app (h.object m.len) =
      h.cylinderProjection.app m ≫ StrictOmegaCategory.Abelianization.unit (h.object m.len) := by
  let a := simplexAtoms h
  let K := SimplexComplex.directedComplex m.len (h.squared m.len)
  let L := StrictOmegaCategory.Abelianization.complex (h.object m.len)
  let b : DirectedComplex.Hom K L := a.fromSimplexChains m.len
  let v : K.realization ⟶ L.realization := b.realization
  let cv : (rightCylinder K).realization ⟶ (rightCylinder L).realization :=
    (RightCylinder.map b).realization
  let pK : (rightCylinder K).realization ⟶ K.realization :=
    (RightCylinder.projection K).realization
  let pL : (rightCylinder L).realization ⟶ L.realization :=
    (RightCylinder.projection L).realization
  have hn : cv ≫ pL = pK ≫ v := by
    apply StrictOmegaCategory.Hom.ext
    funext x
    exact RightCylinder.realization_projection_map b x
  change cv ≫ pL = pK ≫ StrictOmegaCategory.Abelianization.unit (h.object m.len)
  exact hn.trans (congrArg (fun q : K.realization ⟶ L.realization => pK ≫ q)
    (a.unit_eq_realized_inverse m.len).symm)

/-- A map into the extended cylinder with the actual chain comparison has
the prescribed collapse. No invertibility of that map is needed here. -/
theorem extendedComparison_projection (m : SimplexCategory)
    (f : h.cylinderObject m.len ⟶ StrictOmegaCategory.GrayChainExtension.cylinder.obj
      (h.object m.len))
    (hf : f ≫ StrictOmegaCategory.GrayChainExtension.comparison.app (h.object m.len) =
      h.constructedChainModelComparison.hom.app m) :
    f ≫ StrictOmegaCategory.GrayChainExtension.projection.app (h.object m.len) =
      h.cylinderProjection.app m := by
  apply (cancel_mono (h.orientalUnitIso m.len).hom).mp
  rw [h.orientalUnitIso_hom]
  have hp := congrArg (fun q => q.app (h.object m.len))
    StrictOmegaCategory.GrayChainExtension.projection_unit
  change StrictOmegaCategory.GrayChainExtension.projection.app (h.object m.len) ≫
      StrictOmegaCategory.Abelianization.unit (h.object m.len) =
    StrictOmegaCategory.GrayChainExtension.comparison.app (h.object m.len) ≫
      StrictOmegaCategory.GrayChainExtension.modelCollapse.app (h.object m.len) at hp
  let q : StrictOmegaCategory.GrayChainExtension.model.obj (h.object m.len) ⟶
      (StrictOmegaCategory.Abelianization.complex (h.object m.len)).realization :=
    StrictOmegaCategory.GrayChainExtension.modelCollapse.app (h.object m.len)
  let c : StrictOmegaCategory.GrayChainExtension.cylinder.obj (h.object m.len) ⟶
      StrictOmegaCategory.GrayChainExtension.model.obj (h.object m.len) :=
    StrictOmegaCategory.GrayChainExtension.comparison.app (h.object m.len)
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun v => f ≫ v) hp).trans
      (((Category.assoc f c q).symm).trans
        ((congrArg (fun v => v ≫ q) hf).trans
          (h.constructedChainModelComparison_projection m))))

end
end Thomason.Construction.NormalizedSimplexIdentities

end

end OAI
