import OAI.CategoryTheory.Globular.CylinderShapes

namespace OAI

universe u v w

namespace Grothendieck
open CategoryTheory CategoryTheory.Limits Opposite
namespace GlobularFrame
variable {K : Type u} [Category.{v} K] [HasColimitsOfSize.{0,v} K]

@[reassoc] theorem cell_naturality (B : GlobularFrame K) {S T : GlobularPresheaf.{v}}
    (f : S ⟶ T) (k : ℕ) (x : S.underlying.Cell k) :
    B.cell S k x ≫ B.realization.map f = B.cell T k (f.app (op (Globe.mk k)) x) := by
  unfold cell CoGlobularObject.cell
  erw [Category.assoc, ← Functor.map_comp]
  congr 2
  apply uliftYonedaEquiv.injective
  erw [uliftYonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

namespace Hom
variable {D B : GlobularFrame K}
noncomputable def realization (e : Hom D B) : D.realization ⟶ B.realization where
  app S := D.desc ((B.cellMap S).comp (e.pre _))
  naturality S T f := by
    apply D.hom_ext
    intro k x
    erw [cell_naturality_assoc, D.cell_desc]
    erw [← Category.assoc, D.cell_desc]
    change e.obj k ≫ B.cell T k (f.app _ x) = (e.obj k ≫ B.cell S k x) ≫ B.realization.map f
    rw [Category.assoc, cell_naturality]

@[reassoc (attr := simp)] theorem cell_realization (e : Hom D B) (S : GlobularPresheaf.{v})
    (k : ℕ) (x : S.underlying.Cell k) :
    D.cell S k x ≫ e.realization.app S = e.obj k ≫ B.cell S k x := D.cell_desc _ _ _

end Hom

noncomputable abbrev shapeRealization (B : GlobularFrame K) : Shape ⥤ K :=
  Shape.liftedRealization ⋙ B.realization
noncomputable def shapeGlobeIso (B : GlobularFrame K) (j : ℕ) :
    B.shapeRealization.obj (Shape.globe j) ≅ B.obj j :=
  B.realization.mapIso (GlobularPresheaf.liftSmallDiskIso j) ≪≫ B.diagram.globeIso j

noncomputable abbrev Hom.shapeEndpoint {D B : GlobularFrame K} (e : Hom D B) :
    D.shapeRealization ⟶ B.shapeRealization := Functor.whiskerLeft Shape.liftedRealization e.realization

@[reassoc] theorem shapeGlobeIso_cell (B : GlobularFrame K) (j : ℕ) :
    B.cell (Shape.liftedRealization.obj (Shape.globe j)) j (ULift.up (ULift.up (𝟙 (Globe.mk j)))) ≫
      (B.shapeGlobeIso j).hom = 𝟙 _ := by
  dsimp only [shapeGlobeIso, Iso.trans_hom, Functor.mapIso_hom]
  erw [cell_naturality_assoc]
  change B.diagram.cell (GlobularPresheaf.disk j) j (ULift.up (𝟙 (Globe.mk j))) ≫ _ = _
  unfold CoGlobularObject.cell
  have h : (uliftYonedaEquiv.symm (ULift.up (𝟙 (Globe.mk j))) : GlobularPresheaf.disk.{v} j ⟶ _) = 𝟙 _ := by
    apply uliftYonedaEquiv.injective
    rfl
  erw [h]
  erw [B.diagram.realization.map_id (GlobularPresheaf.disk.{v} j), Category.comp_id, Iso.inv_hom_id]
  rfl

theorem shapeGlobeIso_inv_cell (B : GlobularFrame K) (j : ℕ) :
    (B.shapeGlobeIso j).inv = B.cell (Shape.liftedRealization.obj (Shape.globe j)) j
      (ULift.up (ULift.up (𝟙 (Globe.mk j)))) := by
  apply (cancel_mono (B.shapeGlobeIso j).hom).1
  rw [Iso.inv_hom_id, shapeGlobeIso_cell]

@[reassoc] theorem shapeEndpoint_globe {D B : GlobularFrame K} (e : Hom D B) (j : ℕ) :
    (D.shapeGlobeIso j).inv ≫ e.shapeEndpoint.app (Shape.globe j) ≫ (B.shapeGlobeIso j).hom = e.obj j := by
  rw [shapeGlobeIso_inv_cell]
  calc
    _ = (e.obj j ≫ B.cell (Shape.liftedRealization.obj (Shape.globe j)) j
        (ULift.up (ULift.up (𝟙 (Globe.mk j))))) ≫ (B.shapeGlobeIso j).hom := by
      erw [← Category.assoc, Hom.cell_realization]
    _ = e.obj j ≫ (B.cell (Shape.liftedRealization.obj (Shape.globe j)) j
        (ULift.up (ULift.up (𝟙 (Globe.mk j)))) ≫ (B.shapeGlobeIso j).hom) := Category.assoc _ _ _
    _ = e.obj j ≫ 𝟙 _ := congrArg (e.obj j ≫ ·) (B.shapeGlobeIso_cell j)
    _ = e.obj j := Category.comp_id _

@[reassoc] theorem shapeGlobeIso_face (B : GlobularFrame K) {j k : ℕ} (h : j < k) (ε : Bool) :
    B.shapeRealization.map (Shape.face h ε) ≫
      (B.shapeGlobeIso k).hom = (B.shapeGlobeIso j).hom ≫ B.diagram.face h ε := by
  apply (cancel_epi (B.shapeGlobeIso j).inv).1
  erw [Iso.inv_hom_id_assoc]
  rw [shapeGlobeIso_inv_cell]
  erw [cell_naturality_assoc]
  have h' := B.cell_face (Shape.liftedRealization.obj (Shape.globe k)) (Globe.face h ε)
      (ULift.up (ULift.up (𝟙 (Globe.mk k))))
  change B.diagram.face h ε ≫ B.cell (Shape.liftedRealization.obj (Shape.globe k)) k
      (ULift.up (ULift.up (𝟙 (Globe.mk k)))) =
    B.cell (Shape.liftedRealization.obj (Shape.globe k)) j
      (ULift.up (ULift.up (Globe.face h ε))) at h'
  change B.cell (Shape.liftedRealization.obj (Shape.globe k)) j
      (ULift.up (ULift.up (Globe.face h ε))) ≫ (B.shapeGlobeIso k).hom = _
  rw [← h']
  exact (Category.assoc _ _ _).trans ((congrArg (B.diagram.face h ε ≫ ·)
    (B.shapeGlobeIso_cell k)).trans (Category.comp_id _))

end GlobularFrame
end Grothendieck

end OAI
