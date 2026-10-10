import OAI.CategoryTheory.Globular.FrameOperations

namespace OAI

universe u v w

namespace Grothendieck
open CategoryTheory CategoryTheory.Limits Opposite
namespace GlobularTheory.Model
variable {C : GlobularTheory.{v}} (hC : C.IsCoherator) (q n : ℕ)
variable [HasColimitsOfSize.{v,v} (CutoffModels C q)] [HasLimitsOfSize.{v,v} (CutoffModels C q)]
local instance smallColimitsInterpretation : HasColimitsOfSize.{0,v} (CutoffModels C q) :=
  hasColimitsOfSizeShrink.{0,v} (CutoffModels C q)

omit [HasLimitsOfSize.{v,v} (CutoffModels C q)] in
theorem cylinderPair_parallel (a : (cylinderTheory hC q n).AdmissiblePair) :
    (cylinderFrame hC q n).inc a.n ≫ ((cylinderFrame hC q n).shapeGlobeIso a.n).inv ≫ a.source.cylinder =
      (cylinderFrame hC q n).inc a.n ≫ ((cylinderFrame hC q n).shapeGlobeIso a.n).inv ≫ a.target.cylinder := by
  rcases a with ⟨j,S,hS,s,t,hp⟩
  cases j with
  | zero => exact (cylinderFrame hC q n).initial.hom_ext _ _
  | succ j =>
    apply ((cylinderFrame hC q n).square j).hom_ext
    · change (((cylinderFrame hC q n).left j ≫ (cylinderFrame hC q n).inc (j+1))) ≫ _ ≫ s.cylinder =
        (((cylinderFrame hC q n).left j ≫ (cylinderFrame hC q n).inc (j+1))) ≫ _ ≫ t.cylinder
      change (cylinderFrame hC q n).diagram.source j ≫ _ ≫ s.cylinder =
        (cylinderFrame hC q n).diagram.source j ≫ _ ≫ t.cylinder
      have hh (f : (cylinderTheory hC q n).Hom (Shape.globe (j+1)) S) :
          (cylinderFrame hC q n).diagram.source j ≫
              ((cylinderFrame hC q n).shapeGlobeIso (j+1)).inv ≫ f.cylinder =
            ((cylinderFrame hC q n).shapeGlobeIso j).inv ≫
              (cylinderFrame hC q n).shapeRealization.map (Shape.source j) ≫ f.cylinder :=
        (Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ f.cylinder) ((cylinderFrame hC q n).shapeGlobeIso_source_inv j)).trans
            (Category.assoc _ _ _))
      exact (hh s).trans ((congrArg (((cylinderFrame hC q n).shapeGlobeIso j).inv ≫ ·)
        (congrArg RepresentedHom.cylinder hp.1)).trans (hh t).symm)
    · change (((cylinderFrame hC q n).right j ≫ (cylinderFrame hC q n).inc (j+1))) ≫ _ ≫ s.cylinder =
        (((cylinderFrame hC q n).right j ≫ (cylinderFrame hC q n).inc (j+1))) ≫ _ ≫ t.cylinder
      change (cylinderFrame hC q n).diagram.target j ≫ _ ≫ s.cylinder =
        (cylinderFrame hC q n).diagram.target j ≫ _ ≫ t.cylinder
      have hh (f : (cylinderTheory hC q n).Hom (Shape.globe (j+1)) S) :
          (cylinderFrame hC q n).diagram.target j ≫
              ((cylinderFrame hC q n).shapeGlobeIso (j+1)).inv ≫ f.cylinder =
            ((cylinderFrame hC q n).shapeGlobeIso j).inv ≫
              (cylinderFrame hC q n).shapeRealization.map (Shape.target j) ≫ f.cylinder :=
        (Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ f.cylinder) ((cylinderFrame hC q n).shapeGlobeIso_target_inv j)).trans
            (Category.assoc _ _ _))
      exact (hh s).trans ((congrArg (((cylinderFrame hC q n).shapeGlobeIso j).inv ≫ ·)
        (congrArg RepresentedHom.cylinder hp.2)).trans (hh t).symm)

noncomputable def cylinderPairBoundary (a : (cylinderTheory hC q n).AdmissiblePair) :
    (cylinderFrame hC q n).bd (a.n+1) ⟶ (cylinderFrame hC q n).shapeRealization.obj a.arity :=
  ((cylinderFrame hC q n).square a.n).desc
    (((cylinderFrame hC q n).shapeGlobeIso a.n).inv ≫ a.source.cylinder)
    (((cylinderFrame hC q n).shapeGlobeIso a.n).inv ≫ a.target.cylinder)
    (cylinderPair_parallel hC q n a)

omit [HasLimitsOfSize.{v,v} (CutoffModels C q)] in
@[reassoc] theorem cylinderPairBoundary_left (a : (cylinderTheory hC q n).AdmissiblePair) :
    (cylinderFrame hC q n).left a.n ≫ cylinderPairBoundary hC q n a =
      ((cylinderFrame hC q n).shapeGlobeIso a.n).inv ≫ a.source.cylinder :=
  ((cylinderFrame hC q n).square a.n).inl_desc _ _ _
omit [HasLimitsOfSize.{v,v} (CutoffModels C q)] in
@[reassoc] theorem cylinderPairBoundary_right (a : (cylinderTheory hC q n).AdmissiblePair) :
    (cylinderFrame hC q n).right a.n ≫ cylinderPairBoundary hC q n a =
      ((cylinderFrame hC q n).shapeGlobeIso a.n).inv ≫ a.target.cylinder :=
  ((cylinderFrame hC q n).square a.n).inr_desc _ _ _

omit [HasLimitsOfSize.{v,v} (CutoffModels C q)] in
theorem cylinderPairBoundary_endpoint (a : (cylinderTheory hC q n).AdmissiblePair)
    (z : C.Hom (Shape.globe (a.n+1)) a.arity) (hz : Fills (cylinderProjection hC q n) a z) (ε : Bool) :
    (cylinderEndpoint hC q n ε).bd (a.n+1) ≫ cylinderPairBoundary hC q n a =
      (cutoffDiskFrame hC q).inc (a.n+1) ≫ (cutoffRepresentables hC q).map z ≫
        (cylinderShapeEndpoint hC q n ε).app a.arity := by
  let D := cutoffDiskFrame hC q
  let B := cylinderFrame hC q n
  let F := cutoffRepresentables hC q
  let e := cylinderEndpoint hC q n ε
  let E := cylinderShapeEndpoint hC q n ε
  have hs : E.app (Shape.globe a.n) ≫ a.source.cylinder = F.map (show C.toTheoryData.arity.obj (Shape.globe a.n) ⟶ C.toTheoryData.arity.obj a.arity from a.source.original) ≫ E.app a.arity := by
    cases ε
    · exact a.source.endpoint₀
    · exact a.source.endpoint₁
  have ht : E.app (Shape.globe a.n) ≫ a.target.cylinder = F.map (show C.toTheoryData.arity.obj (Shape.globe a.n) ⟶ C.toTheoryData.arity.obj a.arity from a.target.original) ≫ E.app a.arity := by
    cases ε
    · exact a.target.endpoint₀
    · exact a.target.endpoint₁
  apply (D.square a.n).hom_ext
  · change D.left a.n ≫ e.bd (a.n+1) ≫ cylinderPairBoundary hC q n a =
      D.left a.n ≫ D.inc (a.n+1) ≫ F.map (show C.toTheoryData.arity.obj (Shape.globe (a.n+1)) ⟶ C.toTheoryData.arity.obj a.arity from z) ≫ E.app a.arity
    erw [← Category.assoc, e.left, Category.assoc, cylinderPairBoundary_left]
    erw [← Category.assoc, cylinderShapeEndpoint_globe_inv hC q n ε a.n]
    change E.app (Shape.globe a.n) ≫ a.source.cylinder =
      D.diagram.source a.n ≫ F.map (show C.toTheoryData.arity.obj (Shape.globe (a.n+1)) ⟶ C.toTheoryData.arity.obj a.arity from z) ≫ E.app a.arity
    rw [hs]
    have hh : C.comp (C.base (Shape.source a.n)) z = a.source.original := hz.1
    have hz' := congrArg (fun f : C.toTheoryData.arity.obj (Shape.globe a.n) ⟶ C.toTheoryData.arity.obj a.arity => F.map f) hh
    erw [F.map_comp, cutoffRepresentables_source] at hz'
    exact congrArg (· ≫ E.app a.arity) hz'.symm
  · change D.right a.n ≫ e.bd (a.n+1) ≫ cylinderPairBoundary hC q n a =
      D.right a.n ≫ D.inc (a.n+1) ≫ F.map (show C.toTheoryData.arity.obj (Shape.globe (a.n+1)) ⟶ C.toTheoryData.arity.obj a.arity from z) ≫ E.app a.arity
    erw [← Category.assoc, e.right, Category.assoc, cylinderPairBoundary_right]
    erw [← Category.assoc, cylinderShapeEndpoint_globe_inv hC q n ε a.n]
    change E.app (Shape.globe a.n) ≫ a.target.cylinder =
      D.diagram.target a.n ≫ F.map (show C.toTheoryData.arity.obj (Shape.globe (a.n+1)) ⟶ C.toTheoryData.arity.obj a.arity from z) ≫ E.app a.arity
    rw [ht]
    have hh : C.comp (C.base (Shape.target a.n)) z = a.target.original := hz.2
    have hz' := congrArg (fun f : C.toTheoryData.arity.obj (Shape.globe a.n) ⟶ C.toTheoryData.arity.obj a.arity => F.map f) hh
    erw [F.map_comp, cutoffRepresentables_target] at hz'
    exact congrArg (· ≫ E.app a.arity) hz'.symm

theorem cylinderProjection_liftsFillers (hnq : n ≤ q)
    (H : ExpansionContraction hC q (n+1)) : LiftsFillers (cylinderProjection hC q n) := by
  intro a z hz
  let B := cylinderFrame hC q n
  let F := cutoffRepresentables hC q
  let Y := B.shapeRealization.obj a.arity
  let d (ε : Bool) : cutoffDisk hC q (a.n+1) ⟶ Y :=
    F.map (show C.toTheoryData.arity.obj (Shape.globe (a.n+1)) ⟶ C.toTheoryData.arity.obj a.arity from z) ≫ (cylinderShapeEndpoint hC q n ε).app a.arity
  have hd (ε : Bool) : (cylinderNode hC q n (a.n+1)).bdEnd ε ≫
      cylinderPairBoundary hC q n a = cutoffI hC q (a.n+1) ≫ d ε :=
    cylinderPairBoundary_endpoint hC q n a z hz ε
  have hlow (h : a.n+1 < n) : d false = d true := by
    have hh : a.arity.height < n := Nat.lt_of_le_of_lt a.height h
    have heq := cylinderShapeEndpoint_low hC q n a.arity hh
    exact congrArg (fun f : F.obj (C.toTheoryData.arity.obj a.arity) ⟶ Y => F.map (show C.toTheoryData.arity.obj (Shape.globe (a.n+1)) ⟶ C.toTheoryData.arity.obj a.arity from z) ≫ f) heq
  have hY : Y.obj.underlying.HasFillers :=
    (cylinderShape_contractible hC q n hnq H a.arity).2
  obtain ⟨l,hl,he⟩ := cylinderNode_extend hC q n (a.n+1) hY
    (cylinderPairBoundary hC q n a) d hd hlow
  let w : (cylinderTheory hC q n).Hom (Shape.globe (a.n+1)) a.arity :=
    { original := z
      cylinder := (B.shapeGlobeIso (a.n+1)).hom ≫ l
      endpoint₀ := by
        erw [← Category.assoc, cylinderShapeEndpoint_globe hC q n false (a.n+1)]
        exact he false
      endpoint₁ := by
        erw [← Category.assoc, cylinderShapeEndpoint_globe hC q n true (a.n+1)]
        exact he true }
  refine ⟨w, ⟨?_, ?_⟩, rfl⟩
  · apply RepresentedHom.ext hz.1
    change B.shapeRealization.map (Shape.source a.n) ≫ (B.shapeGlobeIso (a.n+1)).hom ≫ l =
      a.source.cylinder
    erw [← Category.assoc, GlobularFrame.shapeGlobeIso_source, Category.assoc]
    change (B.shapeGlobeIso a.n).hom ≫ (B.left a.n ≫ B.inc (a.n+1)) ≫ l = _
    have hh : (B.left a.n ≫ B.inc (a.n+1)) ≫ l =
        (B.shapeGlobeIso a.n).inv ≫ a.source.cylinder :=
      (Category.assoc _ _ _).trans ((congrArg (B.left a.n ≫ ·) hl).trans
        (cylinderPairBoundary_left hC q n a))
    exact (congrArg ((B.shapeGlobeIso a.n).hom ≫ ·) hh).trans
      ((B.shapeGlobeIso a.n).hom_inv_id_assoc _)
  · apply RepresentedHom.ext hz.2
    change B.shapeRealization.map (Shape.target a.n) ≫ (B.shapeGlobeIso (a.n+1)).hom ≫ l =
      a.target.cylinder
    erw [← Category.assoc, GlobularFrame.shapeGlobeIso_target, Category.assoc]
    change (B.shapeGlobeIso a.n).hom ≫ (B.right a.n ≫ B.inc (a.n+1)) ≫ l = _
    have hh : (B.right a.n ≫ B.inc (a.n+1)) ≫ l =
        (B.shapeGlobeIso a.n).inv ≫ a.target.cylinder :=
      (Category.assoc _ _ _).trans ((congrArg (B.right a.n ≫ ·) hl).trans
        (cylinderPairBoundary_right hC q n a))
    exact (congrArg ((B.shapeGlobeIso a.n).hom ≫ ·) hh).trans
      ((B.shapeGlobeIso a.n).hom_inv_id_assoc _)

noncomputable def cylinderInterpretation (hnq : n ≤ q)
    (H : ExpansionContraction hC q (n+1)) : Morphism C (cylinderTheory hC q n) :=
  Classical.choose (hC.1.some.lift (cylinderProjection hC q n)
    (cylinderProjection_liftsFillers hC q n hnq H) (Morphism.id C))

theorem cylinderInterpretation_projection (hnq : n ≤ q) (H : ExpansionContraction hC q (n+1)) :
    (cylinderInterpretation hC q n hnq H).comp (cylinderProjection hC q n) = Morphism.id C :=
  Classical.choose_spec (hC.1.some.lift (cylinderProjection hC q n)
    (cylinderProjection_liftsFillers hC q n hnq H) (Morphism.id C))

end GlobularTheory.Model
end Grothendieck

end OAI
