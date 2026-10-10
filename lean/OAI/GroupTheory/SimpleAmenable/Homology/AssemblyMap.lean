import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.TotalSingle

namespace OAI

section
open CategoryTheory Limits SimplicialObject Simplicial Opposite AlgebraicTopology
open HomologicalComplex HomologicalComplex₂
namespace ModelAssembly

open DiagonalResolution
variable {X Y : Dᵒᵖ ⥤ Type} (φ : X ⟶ Y)
noncomputable def mapCocone (F : D ⥤ A) : Cocone (projection X ⋙ F) where
  pt := (assembly Y).obj F
  ι := {
    app e := colimit.ι (projection Y ⋙ F) (φ.mapElements.op.obj e)
    naturality e e' f := by
      simpa [projection,NatTrans.mapElements,assembly] using
        colimit.w (projection Y ⋙ F) (φ.mapElements.op.map f) }
noncomputable def assemblyMapF (F : D ⥤ A) : (assembly X).obj F ⟶ (assembly Y).obj F :=
  colimit.desc (projection X ⋙ F) (mapCocone φ F)
@[reassoc (attr := simp)] lemma ι_assemblyMapF (F : D ⥤ A) (e : X.Elementsᵒᵖ) :
    colimit.ι (projection X ⋙ F) e ≫ assemblyMapF φ F =
      colimit.ι (projection Y ⋙ F) (φ.mapElements.op.obj e) :=
  colimit.ι_desc _ _
noncomputable def assemblyMap : assembly X ⟶ assembly Y where
  app := assemblyMapF φ
  naturality F G α := by
    apply colimit.hom_ext
    intro e
    change colimit.ι (projection X ⋙ F) e ≫
      colim.map (Functor.whiskerLeft (projection X) α) ≫ assemblyMapF φ G =
      colimit.ι (projection X ⋙ F) e ≫ assemblyMapF φ F ≫
        colim.map (Functor.whiskerLeft (projection Y) α)
    erw [colimit.ι_map_assoc,ι_assemblyMapF,←Category.assoc,ι_assemblyMapF,colimit.ι_map]
    rfl
@[reassoc (attr := simp)] lemma ι_assemblyMap (F : D ⥤ A) (e : X.Elementsᵒᵖ) :
    colimit.ι (projection X ⋙ F) e ≫ (assemblyMap φ).app F =
      colimit.ι (projection Y ⋙ F) (φ.mapElements.op.obj e) :=
  ι_assemblyMapF φ F e
@[reassoc] lemma map_forward (d : D) :
    (assemblyMap φ).app (free d) ≫ forward Y d =
      forward X d ≫ (sigmaConst.obj Z).map (φ.app (op d)) := by
  apply colimit.hom_ext
  intro e
  apply Sigma.hom_ext
  intro f
  change Sigma.ι (fun _ : d ⟶ e.unop.1.unop => Z) f ≫ colimit.ι (projection X ⋙ free d) e ≫ _ = _
  erw [← Category.assoc (colimit.ι (projection X ⋙ free d) e)
    ((assemblyMap φ).app (free d)) (forward Y d), ι_assemblyMap, ι_to]
  change Sigma.ι (fun _ : d ⟶ e.unop.1.unop => Z) f ≫
    (freeCocone Y d).ι.app (φ.mapElements.op.obj e) =
    Sigma.ι (fun _ : d ⟶ e.unop.1.unop => Z) f ≫
    colimit.ι (projection X ⋙ free d) e ≫ forward X d ≫ _
  erw [← Category.assoc (colimit.ι (projection X ⋙ free d) e) (forward X d)
    ((sigmaConst.obj Z).map (φ.app (op d))), ι_to]
  dsimp only [freeCocone]
  erw [Sigma.ι_comp_desc, Sigma.ι_comp_desc_assoc]
  dsimp only [sigmaConst]
  erw [Sigma.ι_comp_map', Category.id_comp]
  congr 1
  exact (ConcreteCategory.congr_hom (φ.naturality f.op) e.unop.2).symm
end ModelAssembly

end

open CategoryTheory Limits HomologicalComplex HomologicalComplex₂
namespace TotalFunctor

universe u v u' v'
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{0} C]
  {E : Type u'} [Category.{v'} E] [Preadditive E] [HasCoproducts.{0} E]
open TotalHomotopy
variable {F G : C ⥤ E} [F.Additive] [G.Additive] (α : F ⟶ G)
noncomputable abbrev nat₂ (K : HomologicalComplex₂ C c c) : map₂ F K ⟶ map₂ G K :=
  ((α.mapHomologicalComplex c).mapHomologicalComplex c).app K
@[reassoc] lemma comparison_natural (K : HomologicalComplex₂ C c c) :
    total.map (nat₂ α K) c ≫ comparison G K =
      comparison F K ≫ (α.mapHomologicalComplex c).app (K.total c) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply total.hom_ext
  intro p q hpq
  change (map₂ F K).ιTotal c p q n hpq ≫ (total.map (nat₂ α K) c).f n ≫ comparisonF G K n =
    (map₂ F K).ιTotal c p q n hpq ≫ comparisonF F K n ≫ α.app _
  rw [ιTotal_map_assoc,ι_comparisonF,ι_comparisonF_assoc]
  exact (α.naturality _).symm
@[reassoc] lemma iso_natural [PreservesColimitsOfSize.{0,0} F] [PreservesColimitsOfSize.{0,0} G]
    (K : HomologicalComplex₂ C c c) :
    (α.mapHomologicalComplex c).app (K.total c) ≫ (iso G K).hom =
      (iso F K).hom ≫ total.map (nat₂ α K) c := by
  apply (cancel_mono (comparison G K)).mp
  simp only [Category.assoc]
  change _ ≫ inv (comparison G K) ≫ comparison G K =
    inv (comparison F K) ≫ total.map (nat₂ α K) c ≫ comparison G K
  rw [IsIso.inv_hom_id,Category.comp_id,comparison_natural,←Category.assoc,
    IsIso.inv_hom_id,Category.id_comp]
end TotalFunctor

end OAI
