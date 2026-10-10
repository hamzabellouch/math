import OAI.CategoryTheory.Thomason.Representation
import OAI.CategoryTheory.Thomason.Gray.ConstructedRightGray

namespace OAI

/-! The globe-and-pasting construction gives a right interval adjunction on
strict omega-categories. The equivalence of cell presentations transports
its ordered simplex comparisons, endpoints, collapse and finite truncations. -/

namespace Thomason.ConstructedInterval

open CategoryTheory CategoryTheory.Functor Construction Construction.StrictOmegaCategory

noncomputable section

/-- The global right interval tensor in the separate-boundary presentation. -/
def tensor : OmegaCategory.{0} ⥤ OmegaCategory.{0} :=
  fromOmega ⋙ GrayChainExtension.cylinder ⋙ toOmega

/-- The right internal hom whose cells are maps from concrete globe cylinders. -/
def internalHom : OmegaCategory.{0} ⥤ OmegaCategory.{0} :=
  fromOmega ⋙ GrayMapping.internalHom ⋙ toOmega

/-- Transport of the global right interval adjunction preserves its actual functors. -/
def adjunction : tensor ⊣ internalHom :=
  representationEquivalence.symm.toAdjunction.comp
    (GrayMapping.adjunction.comp representationEquivalence.toAdjunction)

/-- The two oriented endpoint maps of the transported cylinder. -/
def endpoint (side : Bool) : 𝟭 OmegaCategory.{0} ⟶ tensor :=
  representationEquivalence.counitIso.inv ≫
    whiskerLeft fromOmega (whiskerRight (GrayChainExtension.endpoint side) toOmega)

/-- Collapse of the transported cylinder to its source. -/
def projection : tensor ⟶ 𝟭 OmegaCategory.{0} :=
  whiskerLeft fromOmega (whiskerRight GrayChainExtension.projection toOmega) ≫
    representationEquivalence.counitIso.hom

@[simp] theorem endpoint_projection (side : Bool) (C : OmegaCategory.{0}) :
    (endpoint side).app C ≫ projection.app C = 𝟙 C := by
  change (representationEquivalence.counitIso.inv.app C ≫
      toOmega.map ((GrayChainExtension.endpoint side).app (fromOmega.obj C))) ≫
    (toOmega.map (GrayChainExtension.projection.app (fromOmega.obj C)) ≫
      representationEquivalence.counitIso.hom.app C) = 𝟙 C
  erw [Category.assoc, ← Category.assoc (toOmega.map _) (toOmega.map _),
    ← toOmega.map_comp, GrayChainExtension.endpoint_projection, toOmega.map_id,
    Category.id_comp]
  exact representationEquivalence.counitIso.inv_hom_id_app C

/-- Conversion of the source presentation commutes naturally with the tensor. -/
def representationComparison :
    toOmega ⋙ tensor ≅ GrayChainExtension.cylinder ⋙ toOmega :=
  representationEquivalence.funInvIdAssoc (GrayChainExtension.cylinder ⋙ toOmega)

theorem representationComparison_endpoint (side : Bool) (C : StrictOmegaCategory.{0}) :
    toOmega.map ((GrayChainExtension.endpoint side).app C) ≫
      representationComparison.inv.app C = (endpoint side).app (toOmega.obj C) := by
  erw [representationComparison, Equivalence.funInvIdAssoc_inv_app]
  change toOmega.map ((GrayChainExtension.endpoint side).app C) ≫
      toOmega.map (GrayChainExtension.cylinder.map (representationEquivalence.unit.app C)) =
    representationEquivalence.counitInv.app (toOmega.obj C) ≫
      toOmega.map ((GrayChainExtension.endpoint side).app (fromOmega.obj (toOmega.obj C)))
  erw [← toOmega.map_comp, ← (GrayChainExtension.endpoint side).naturality,
    toOmega.map_comp, representationEquivalence.counitInv_app_functor]
  rfl

theorem representationComparison_projection (C : StrictOmegaCategory.{0}) :
    representationComparison.inv.app C ≫ projection.app (toOmega.obj C) =
      toOmega.map (GrayChainExtension.projection.app C) := by
  erw [representationComparison, Equivalence.funInvIdAssoc_inv_app]
  change toOmega.map (GrayChainExtension.cylinder.map (representationEquivalence.unit.app C)) ≫
    (toOmega.map (GrayChainExtension.projection.app (fromOmega.obj (toOmega.obj C))) ≫
      representationEquivalence.counit.app (toOmega.obj C)) =
        toOmega.map (GrayChainExtension.projection.app C)
  have hn : GrayChainExtension.cylinder.map (representationEquivalence.unit.app C) ≫
      GrayChainExtension.projection.app (fromOmega.obj (toOmega.obj C)) =
      GrayChainExtension.projection.app C ≫ representationEquivalence.unit.app C :=
    GrayChainExtension.projection.naturality (representationEquivalence.unit.app C)
  erw [← Category.assoc, ← toOmega.map_comp, hn, toOmega.map_comp]

/-- The same right internal hom preserves each finite dimension bound. -/
theorem internalHom_isTruncated {Y : OmegaCategory.{0}} {n : ℕ}
    (hY : Y.IsTruncated n) : (internalHom.obj Y).IsTruncated n := by
  change (GrayMapping.internalHom.obj (fromOmega.obj Y)).toOmegaCategory.IsTruncated n
  apply (StrictOmegaCategory.toOmegaCategory_isTruncated _ n).mpr
  apply GrayChainExtension.rightAdjoint_truncated GrayMapping.adjunction
  exact (Y.toStrictOmegaCategory_isTruncated n).mpr hY

variable (h : NormalizedSimplexIdentities)

/-- The ordered simplex cylinder compares naturally with the global right tensor. -/
def simplexComparison :
    h.cylinderCosimplicial ⋙ toOmega ≅ (h.cosimplicial ⋙ toOmega) ⋙ tensor :=
  isoWhiskerRight h.constructedRightSimplexComparison toOmega ≪≫
    isoWhiskerLeft h.cosimplicial representationComparison.symm

/-- The ordered comparison respects both endpoint conventions. -/
theorem simplexComparison_endpoint (side : Bool) (m : SimplexCategory) :
    toOmega.map ((h.cylinderEndpoint side).app m) ≫ (simplexComparison h).hom.app m =
      (endpoint side).app (toOmega.obj (h.object m.len)) := by
  change toOmega.map ((h.cylinderEndpoint side).app m) ≫
      (toOmega.map (h.constructedRightSimplexComparison.hom.app m) ≫
        representationComparison.inv.app (h.object m.len)) = _
  erw [← Category.assoc, ← toOmega.map_comp,
    h.constructedRightSimplexComparison_endpoint]
  exact representationComparison_endpoint side _

/-- The ordered comparison respects collapse of the interval. -/
theorem simplexComparison_projection (m : SimplexCategory) :
    (simplexComparison h).hom.app m ≫ projection.app (toOmega.obj (h.object m.len)) =
      toOmega.map (h.cylinderProjection.app m) := by
  change (toOmega.map (h.constructedRightSimplexComparison.hom.app m) ≫
      representationComparison.inv.app (h.object m.len)) ≫ _ = _
  erw [Category.assoc, representationComparison_projection, ← toOmega.map_comp,
    h.constructedRightSimplexComparison_projection]
  rfl

end

end Thomason.ConstructedInterval

end OAI
