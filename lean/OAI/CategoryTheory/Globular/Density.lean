import OAI.CategoryTheory.Globular.LinearShape

namespace OAI

universe u v w

namespace Grothendieck
open CategoryTheory CategoryTheory.Limits Opposite

namespace GlobularPresheaf

noncomputable def densityDesc {K : Type u} [Category.{v} K]
    (F : GlobularPresheaf.{0} ⥤ K) [PreservesColimitsOfSize.{0,0} F]
    (S : GlobularPresheaf.{0}) (Y : K)
    (d : ∀ (k : Globe), S.obj (op k) → (F.obj (uliftYoneda.obj k) ⟶ Y))
    (hd : ∀ {k l : Globe} (f : k ⟶ l) x,
      F.map (uliftYoneda.map f) ≫ d l x = d k (S.map f.op x)) : F.obj S ⟶ Y :=
  (isColimitOfPreserves F (Presheaf.colimitOfRepresentable S)).desc
    { pt := Y
      ι :=
        { app x := d x.unop.1.unop x.unop.2
          naturality x y f := by
            dsimp
            erw [Category.comp_id]
            exact (hd f.unop.1.unop y.unop.2).trans (congrArg (d x.unop.1.unop) f.unop.2) } }

@[reassoc (attr := simp)] theorem densityDesc_cell {K : Type u} [Category.{v} K]
    (F : GlobularPresheaf.{0} ⥤ K) [PreservesColimitsOfSize.{0,0} F]
    (S : GlobularPresheaf.{0}) (Y : K) (d) (hd) (k : Globe) (x : S.obj (op k)) :
    F.map (uliftYonedaEquiv.symm x) ≫ densityDesc F S Y d hd = d k x := by
  exact (isColimitOfPreserves F (Presheaf.colimitOfRepresentable S)).fac _
    (op (Functor.elementsMk S (op k) x))

theorem density_hom_ext {K : Type u} [Category.{v} K]
    (F : GlobularPresheaf.{0} ⥤ K) [PreservesColimitsOfSize.{0,0} F]
    {S : GlobularPresheaf.{0}} {Y : K} {f g : F.obj S ⟶ Y}
    (h : ∀ (k : Globe) (x : S.obj (op k)),
      F.map (uliftYonedaEquiv.symm x) ≫ f = F.map (uliftYonedaEquiv.symm x) ≫ g) : f = g := by
  apply (isColimitOfPreserves F (Presheaf.colimitOfRepresentable S)).hom_ext
  intro x
  exact h x.unop.1.unop x.unop.2

noncomputable def liftSmall : GlobularPresheaf.{0} ⥤ GlobularPresheaf.{v} :=
  (Functor.whiskeringRight Globeᵒᵖ (Type) (Type v)).obj uliftFunctor.{v,0}

instance liftSmall_preservesColimits : PreservesColimitsOfSize.{0,0} (liftSmall.{v}) := by
  unfold liftSmall
  infer_instance

end GlobularPresheaf

namespace GlobularTheory.Model

noncomputable def smallFree {C : GlobularTheory.{v}} (hC : C.IsCoherator) (q : ℕ) :
    GlobularPresheaf.{0} ⥤ CutoffModels C q :=
  GlobularPresheaf.liftSmall.{v} ⋙ cutoffFreeGlobular hC q

instance smallFree_preservesColimits {C : GlobularTheory.{v}} (hC : C.IsCoherator) (q : ℕ) :
    PreservesColimitsOfSize.{0,0} (smallFree hC q) := by
  let : PreservesColimitsOfSize.{0,0} (cutoffFreeGlobular hC q) :=
    preservesColimitsOfSize_shrink _
  unfold smallFree
  infer_instance

noncomputable def cutoffShapeEquiv {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) (S : Shape) (Y : CutoffModels C q) :
    ((cutoffFunctor hC q).obj (freeShape C S) ⟶ Y) ≃
      (GlobularPresheaf.liftSmall.obj S.realize ⟶ (cutoffForgetGlobular C q).obj Y) :=
  ((cutoffAdjunction hC q).homEquiv _ Y).trans (shapeGlobularEquiv S Y.obj)

@[reassoc] theorem cutoffShapeEquiv_naturality {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) (S : Shape) {Y Z : CutoffModels C q}
    (a : (cutoffFunctor hC q).obj (freeShape C S) ⟶ Y) (b : Y ⟶ Z) :
    cutoffShapeEquiv hC q S Z (a ≫ b) =
      cutoffShapeEquiv hC q S Y a ≫ (cutoffForgetGlobular C q).map b := by
  change shapeGlobularEquiv S Z.obj
    ((cutoffAdjunction hC q).homEquiv _ Z (a ≫ b)) =
    shapeGlobularEquiv S Y.obj ((cutoffAdjunction hC q).homEquiv _ Y a) ≫ _
  erw [Adjunction.homEquiv_naturality_right, shapeGlobularEquiv_natural]
  rfl

noncomputable def smallFreeShapeIso {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) (S : Shape) :
    (smallFree hC q).obj S.realize ≅ (cutoffFunctor hC q).obj (freeShape C S) := by
  let U := cutoffForgetGlobular C q
  let A := cutoffGlobularAdjunction hC q
  let P := (cutoffFunctor hC q).obj (freeShape C S)
  let X := GlobularPresheaf.liftSmall.obj S.realize
  let E (Y : CutoffModels C q) := cutoffShapeEquiv hC q S Y
  let f := (A.homEquiv X P).symm (E P (𝟙 P))
  let g := (E ((cutoffFreeGlobular hC q).obj X)).symm (A.unit.app X)
  have hf : A.homEquiv X P f = E P (𝟙 P) := (A.homEquiv X P).apply_symm_apply _
  have hg : E ((cutoffFreeGlobular hC q).obj X) g = A.unit.app X := (E _).apply_symm_apply _
  refine ⟨f, g, ?_, ?_⟩
  · apply (A.homEquiv X _).injective
    erw [Adjunction.homEquiv_naturality_right, hf, Adjunction.homEquiv_id]
    change E P (𝟙 P) ≫ U.map g = _
    erw [← cutoffShapeEquiv_naturality]
    erw [Category.id_comp]
    exact hg
  · apply (E P).injective
    change E P (g ≫ f) = E P (𝟙 P)
    erw [cutoffShapeEquiv_naturality, hg]
    exact hf

theorem smallFree_cofibrant {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) (S : GlobularPresheaf.{0}) : Cofibrant hC q ((smallFree hC q).obj S) :=
  cutoffFreeGlobular_cofibrant hC q _

noncomputable def smallFreeGen {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) (S : GlobularPresheaf.{0}) (k : ℕ) (x : S.underlying.Cell k) :
    ((smallFree hC q).obj S).obj.underlying.Cell k :=
  (GlobularPresheaf.underlyingMap
    ((cutoffGlobularAdjunction hC q).unit.app (GlobularPresheaf.liftSmall.obj S))).app k
      (ULift.up x)

noncomputable def smallFreeDesc {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) {S : GlobularPresheaf.{0}} {Y : CutoffModels C q}
    (f : GlobularSet.Hom (GlobularPresheaf.liftSmall.obj S).underlying Y.obj.underlying) :
    (smallFree hC q).obj S ⟶ Y :=
  ((cutoffGlobularAdjunction hC q).homEquiv _ Y).symm
    ((GlobularPresheaf.liftSmall.obj S).underlyingPresheafIso.inv ≫
      f.presheafMap ≫ ((cutoffForgetGlobular C q).obj Y).underlyingPresheafIso.hom)

@[simp] theorem smallFreeDesc_gen {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) {S : GlobularPresheaf.{0}} {Y : CutoffModels C q}
    (f : GlobularSet.Hom (GlobularPresheaf.liftSmall.obj S).underlying Y.obj.underlying)
    (k : ℕ) (x : S.underlying.Cell k) :
    (underlyingMap (smallFreeDesc hC q f).hom).app k (smallFreeGen hC q S k x) =
      f.app k (ULift.up x) := by
  have h := ((cutoffGlobularAdjunction hC q).homEquiv _ Y).apply_symm_apply
    ((GlobularPresheaf.liftSmall.obj S).underlyingPresheafIso.inv ≫
      f.presheafMap ≫ ((cutoffForgetGlobular C q).obj Y).underlyingPresheafIso.hom)
  exact congrFun (congrArg (fun z => (GlobularPresheaf.underlyingMap z).app k) h) (ULift.up x)

@[simp] theorem smallFreeGen_source {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) (S : GlobularPresheaf.{0}) (k : ℕ) (x : S.underlying.Cell (k+1)) :
    ((smallFree hC q).obj S).obj.underlying.source k (smallFreeGen hC q S (k+1) x) =
      smallFreeGen hC q S k (S.underlying.source k x) := by
  exact (GlobularPresheaf.underlyingMap
    ((cutoffGlobularAdjunction hC q).unit.app (GlobularPresheaf.liftSmall.obj S))).source_app k
      (ULift.up x) |>.symm

@[simp] theorem smallFreeGen_target {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) (S : GlobularPresheaf.{0}) (k : ℕ) (x : S.underlying.Cell (k+1)) :
    ((smallFree hC q).obj S).obj.underlying.target k (smallFreeGen hC q S (k+1) x) =
      smallFreeGen hC q S k (S.underlying.target k x) := by
  exact (GlobularPresheaf.underlyingMap
    ((cutoffGlobularAdjunction hC q).unit.app (GlobularPresheaf.liftSmall.obj S))).target_app k
      (ULift.up x) |>.symm

@[simp] theorem smallFreeGen_map {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) {S T : GlobularPresheaf.{0}} (f : S ⟶ T) (k : ℕ) (x : S.underlying.Cell k) :
    (underlyingMap ((smallFree hC q).map f).hom).app k (smallFreeGen hC q S k x) =
      smallFreeGen hC q T k ((GlobularPresheaf.underlyingMap f).app k x) := by
  have h := (cutoffGlobularAdjunction hC q).unit.naturality
    (GlobularPresheaf.liftSmall.map f)
  exact (congrFun (congrArg (fun z => (GlobularPresheaf.underlyingMap z).app k) h)
    (ULift.up x)).symm

end GlobularTheory.Model
end Grothendieck

end OAI
