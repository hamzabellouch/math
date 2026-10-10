import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.ConcurrentCellSlopeAction
import OAI.GroupTheory.SimpleAmenable.CentralCovers.GridFormalPatching
import OAI.GroupTheory.SimpleAmenable.CentralCovers.PrimitiveChartActions
import OAI.GroupTheory.SimpleAmenable.CentralCovers.TemplateRelators
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.ConcurrentCellDecisions
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.VaryingCellClassification

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section CrossingCellActions

@[simp] theorem integralCutForm_neg (a : ℕ) (j : Fin 4) (z : CutRing × CutRing) :
    integralCutForm a j (-z) = -integralCutForm a j z := by
  fin_cases j <;> simp [integralCutForm] <;> ring

namespace InitialCoverSystem.PatchAtlas
variable {a m M : ℕ} {r : CutRing} {hm : 2  ≤  m}
    {B : InitialCoverSystem a r m hm M}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (A : B.PatchAtlas)

noncomputable def concurrentPrimitives (t : VertexType (commonVertexDenominator a))
    (u : CutRing × CutRing) :
    Sum (Fin 4) (Fin 2 × Fin (A.geometry.window-1)) → Fin 5 × (CutRing × CutRing) :=
  translatedTemplate (Sum.elim
    (fun j : Fin 4 => (⟨j.val+1,by omega⟩,A.geometry.anchors t j))
    (coordinateWindowPrimitives A.geometry.window A.geometry.start)) u

omit [Group.IsPerfect (alternatingGroup (Fin (m+1)))] in
theorem concurrentLaw (t : VertexType (commonVertexDenominator a)) (u : CutRing × CutRing) :
    ∀ I (_ : I.card ≤ 15) b hb, B.PrimitiveFamilyLaw I b hb (A.concurrentPrimitives t u) :=
  fun I _ b hb => A.concurrent t u I b hb

noncomputable def margin (t : VertexType (commonVertexDenominator a)) (u : CutRing × CutRing) :
    polygonAlgebra a := spatialTranslate u
    (coordinateRectangle a (A.geometry.margins t).lower (A.geometry.margins t).upper)

theorem crossing_cell_actions {ι κ : Type*} [Finite ι] [Finite κ]
    (hlarge : 20 ≤ m+1) (hr : 0<ordinary r ∧ ordinary r<1/2) (ha : 0<a)
    (P : ι → Fin 5 × (CutRing × CutRing)) (Q : κ → Fin 5 × (CutRing × CutRing))
    (h : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb P)
    (g : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb Q)
    (i : ι) (i' : κ) (d j : Fin 2) (v : CutRing × CutRing)
    (hP : P i=(slopeTestIndex d,0)) (hQ : Q i'=(coordinateTestIndex j,v))
    (q : Fin 2 → ℤ) (cell : Fin 2 → Fin A.geometry.mesh)
    (k : Fin 2 → ℤ) (c : CutRing) (positive : Bool)
    (hk : ∀ l, -ordinary r ≤ ordinary (windowCut A.geometry.mesh (q l) (cell l).castSucc)+(k l:ℝ) ∧
      ordinary (windowCut A.geometry.mesh (q l) (cell l).succ)+(k l:ℝ) ≤ ordinary r)
    (hc : ∀ p ∈ (windowRectangle a A.geometry.mesh q cell).val,
      (p ∈ (spatialTranslate v (coordinatePrimitive a j)).val ↔
        if positive then ordinary c ≤ realCoordinate (windowPlanarLift q p) j
        else realCoordinate (windowPlanarLift q p) j<ordinary c))
    (x y v' w : GenericSquare a)
    (hx : x ∈ (windowRectangle a A.geometry.mesh q cell).val)
    (hy : y ∈ (windowRectangle a A.geometry.mesh q cell).val)
    (hv : v' ∈ (windowRectangle a A.geometry.mesh q cell).val)
    (hw : w ∈ (windowRectangle a A.geometry.mesh q cell).val)
    (hcx : cutForm a (slopeDirection d) (windowPlanarLift q x) ≤
      ordinary (-integralCutForm a (slopeDirection d) ((k 0:CutRing),(k 1:CutRing))))
    (hcy : ordinary (-integralCutForm a (slopeDirection d) ((k 0:CutRing),(k 1:CutRing))) ≤
      cutForm a (slopeDirection d) (windowPlanarLift q y))
    (hdv : cutForm a (axisDirection j) (windowPlanarLift q v') ≤ ordinary c)
    (hdw : ordinary c ≤ cutForm a (axisDirection j) (windowPlanarLift q w)) :
    ∃ t : VertexType (commonVertexDenominator a), ∃ u : CutRing × CutRing,
      windowRectangle a A.geometry.mesh q cell ≤ A.margin t u ∧
      ∀ f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm),
        B.AlignedSmallSupported f →
        SmallControlled B.c f (B.windowSector (by omega) A.geometry.mesh
          (A.rectangles.rectangles A.geometry.mesh) q (windowRectangle a A.geometry.mesh q cell)) →
        ∀ (I : ControlAlphabet (Fin (m+1))) (s : UniversalExtension (alternatingGroup I.val)),
          ∀ b ∈ f.range,
            (B.fullGeometricSector (by omega) P h (clippedSlopePrimitive a r (slopeDirection d))
                (universalMap (subtypeAlternatingHom I.val) s)*b*
              (B.fullGeometricSector (by omega) P h (clippedSlopePrimitive a r (slopeDirection d))
                (universalMap (subtypeAlternatingHom I.val) s))⁻¹ =
            B.fullGeometricSector (by omega) (A.concurrentPrimitives t u) (A.concurrentLaw t u)
                (spatialTranslate (u+A.geometry.anchors t (slopeDirection d))
                  (clippedSlopePrimitive a r (slopeDirection d)))
                (universalMap (subtypeAlternatingHom I.val) s)*b*
              (B.fullGeometricSector (by omega) (A.concurrentPrimitives t u) (A.concurrentLaw t u)
                (spatialTranslate (u+A.geometry.anchors t (slopeDirection d))
                  (clippedSlopePrimitive a r (slopeDirection d)))
                (universalMap (subtypeAlternatingHom I.val) s))⁻¹) ∧
            (B.fullGeometricSector (by omega) Q g (spatialTranslate v (coordinatePrimitive a j))
                (universalMap (subtypeAlternatingHom I.val) s)*b*
              (B.fullGeometricSector (by omega) Q g (spatialTranslate v (coordinatePrimitive a j))
                (universalMap (subtypeAlternatingHom I.val) s))⁻¹ =
            B.fullGeometricSector (by omega) (A.concurrentPrimitives t u) (A.concurrentLaw t u)
                (if positive then spatialTranslate (u+A.geometry.anchors t (axisDirection j)) (coordinatePrimitive a j)
                  else (spatialTranslate (u+A.geometry.anchors t (axisDirection j)) (coordinatePrimitive a j))ᶜ)
                (universalMap (subtypeAlternatingHom I.val) s)*b*
              (B.fullGeometricSector (by omega) (A.concurrentPrimitives t u) (A.concurrentLaw t u)
                (if positive then spatialTranslate (u+A.geometry.anchors t (axisDirection j)) (coordinatePrimitive a j)
                  else (spatialTranslate (u+A.geometry.anchors t (axisDirection j)) (coordinatePrimitive a j))ᶜ)
                (universalMap (subtypeAlternatingHom I.val) s))⁻¹) := by
  let z : CutRing × CutRing := -((k 0:CutRing),(k 1:CutRing))
  have hclip : ∀ l, -ordinary r ≤ ordinary (windowCut A.geometry.mesh (q l) (cell l).castSucc)-
      ordinary (pointCoordinate z l) ∧
    ordinary (windowCut A.geometry.mesh (q l) (cell l).succ)-ordinary (pointCoordinate z l) ≤ ordinary r := by
    intro l
    fin_cases l <;> simpa [z,pointCoordinate] using hk _
  obtain ⟨t,u,hline,haxis,hmargin,hnear,hact⟩ := A.rectangles.concurrent_cell_slope_action A.geometry
    hlarge hr ha q cell d (axisDirection j) (slopeDirection_ne_axisDirection d j) z c hclip
    x y v' w hx hy hv hw (by simpa only [z,integralCutForm_neg] using hcx) (by simpa only [z,integralCutForm_neg] using hcy) hdv hdw
  refine ⟨t,u,A.geometry.cell_le_margin hr.2 q cell t u hmargin,fun f hf hfW I s b hb => ?_⟩
  have e₀ := A.rectangles.slope_chart_eq (by omega) P h i d 0 hP
  rw [spatialTranslate_zero] at e₀
  have e₁ := A.rectangles.slope_chart_eq (by omega) (A.concurrentPrimitives t u)
    (A.concurrentLaw t u) (Sum.inl (slopeDirection d)) d
    (u+A.geometry.anchors t (slopeDirection d)) rfl
  have ez : A.rectangles.slope (by omega) d z=A.rectangles.slope (by omega) d 0 := by
    simpa [RectangularAtlas.slope,z] using B.tangentSign_integral (by omega)
      A.rectangles.k A.rectangles.p A.rectangles.u A.rectangles.charts d (fun l => -k l) true
  constructor
  · rw [← e₀,← e₁,← ez]
    exact hact f hf hfW I s b hb
  · apply B.primitive_coordinate_action hlarge A.rectangles.rectangles Q
      (A.concurrentPrimitives t u) g (A.concurrentLaw t u) i' (Sum.inl (axisDirection j))
      j j v (u+A.geometry.anchors t (axisDirection j)) hQ rfl _ _ _
      (fun _ _ he => he ()) ?_ A.geometry.mesh q
      (windowRectangle_resolved A.geometry.mesh (by have hh := A.geometry.mesh_large; omega) q cell)
      (A.geometry.cell_axis_eq q cell j v c positive hc t u haxis hmargin
        (hnear (axisDirection j) (by simp))) f hf hfW I s b hb
    cases positive with
    | false => exact fun _ _ he => not_congr (he ())
    | true => exact fun _ _ he => he ()

end InitialCoverSystem.PatchAtlas
end CrossingCellActions

section LocalPatchTemplates
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) {ι J : Type*}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

structure LocalPatchTemplate (hlarge : 15 < m+1)
    (F : Option ι → TrackStar (Fin (m+1)) →*
      BoundedRelationCover M (alternatingGenerator a r m hm))
    (f : J → TrackStar (Fin (m+1)) →*
      BoundedRelationCover M (alternatingGenerator a r m hm)) where
  index : Type
  [finite_index : Finite index]
  tests : index → Fin 5 × (CutRing × CutRing)
  lawful : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb tests
  margin : polygonAlgebra a
  predicates : ι → polygonAlgebra a
  margin_resolved : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) tests i).val) margin.val
  predicates_resolved : ∀ j, ResolvedBy (fun i => (primitiveTests (a := a) (r := r) tests i).val) (predicates j).val
  controlled : ∀ j, SmallControlled B.c (f j) (B.fullGeometricSector hlarge tests lawful margin)
  action : ∀ i (I : FiveAlphabet (Fin (m+1))) s j, ∀ x ∈ (f j).range,
    F (some i) (universalMap (subtypeAlternatingHom I.val) s)*x*
      (F (some i) (universalMap (subtypeAlternatingHom I.val) s))⁻¹ =
    B.fullGeometricSector hlarge tests lawful (predicates i)
        (universalMap (subtypeAlternatingHom I.val) s)*x*
      (B.fullGeometricSector hlarge tests lawful (predicates i)
        (universalMap (subtypeAlternatingHom I.val) s))⁻¹

attribute [instance] LocalPatchTemplate.finite_index

namespace LocalPatchTemplate
variable {B} {F : Option ι → TrackStar (Fin (m+1)) →*
      BoundedRelationCover M (alternatingGenerator a r m hm)}
    {f : J → TrackStar (Fin (m+1)) →*
      BoundedRelationCover M (alternatingGenerator a r m hm)}
    {hlarge : 15 < m+1} (T : B.LocalPatchTemplate hlarge F f)

theorem masked_actions (h20 : 20 ≤ m+1)
    (hF : F none=B.c.comp (universalProjection (alternatingGroup (Fin (m+1)))))
    (hf : ∀ j, B.AlignedSmallSupported (f j)) :
    ∀ i (I : FiveAlphabet (Fin (m+1))) s j, ∀ x ∈ (f j).range,
      F i (universalMap (subtypeAlternatingHom I.val) s)*x*
        (F i (universalMap (subtypeAlternatingHom I.val) s))⁻¹ =
      B.fullGeometricSector hlarge T.tests T.lawful (marginFamily T.predicates T.margin i)
          (universalMap (subtypeAlternatingHom I.val) s)*x*
        (B.fullGeometricSector hlarge T.tests T.lawful (marginFamily T.predicates T.margin i)
          (universalMap (subtypeAlternatingHom I.val) s))⁻¹ := by
  intro i I s j x hx
  let I' : ControlAlphabet (Fin (m+1)) := ⟨I.val,by rw [I.property.2]; omega⟩
  cases i with
  | none =>
    have hh := B.cell_restrict_action h20 T.tests T.lawful (wholePolygon a) T.margin
      (fun _ _ _ => Iff.rfl) T.margin_resolved (f j) (hf j) (T.controlled j) I' s x hx
    rw [B.fullGeometricSector_whole,← hF] at hh
    have he : wholePolygon a ⊓ T.margin=T.margin := top_inf_eq _
    rw [he] at hh
    exact hh
  | some i =>
    exact (T.action i I s j x hx).trans (by
      simpa only [marginFamily,inf_comm] using B.cell_restrict_action h20 T.tests T.lawful
        (T.predicates i) T.margin (T.predicates_resolved i) T.margin_resolved
        (f j) (hf j) (T.controlled j) I' s x hx)

end LocalPatchTemplate

theorem grid_formal_patching_templates {ι D : Type*} [Finite ι] [Fintype D]
    {κ : Option ι → Type*} [∀ i, Finite (κ i)]
    (hlarge : 25 ≤ m+1)
    (Q : (i : Option ι) → κ i → Fin 5 × (CutRing × CutRing))
    (h : ∀ i I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb (Q i))
    (U : Option ι → polygonAlgebra a) (W : D → polygonAlgebra a)
    (hU : ∀ i, ResolvedBy (fun j => (primitiveTests (a := a) (r := r) (Q i) j).val) (U i).val)
    (hW : ∀ i d, ResolvedBy (fun j => (primitiveTests (a := a) (r := r) (Q i) j).val) (W d).val)
    (he : ∀ i d, B.fullGeometricSector (by omega) (Q i) (h i) (W d)=
      B.fullGeometricSector (by omega) (Q none) (h none) (W d))
    (hdisjoint : Pairwise fun d e => Disjoint (W d).val (W e).val)
    (hcover : ∀ x, ∃ d, x ∈ (W d).val)
    (f : (I : FiveAlphabet (Fin (m+1))) → Option ι → alternatingGroup I.val →*
      BoundedRelationCover M (alternatingGenerator a r m hm))
    (hspec : ∀ I i, (B.gridInput (by omega) Q h U i).comp (universalMap (subtypeAlternatingHom I.val))=
      (f I i).comp (universalProjection (alternatingGroup I.val)))
    (hconst : U none=wholePolygon a)
    (hlocal : ∀ d, Nonempty (B.LocalPatchTemplate (by omega)
      (B.gridInput (by omega) Q h U) (B.gridPiece (by omega) Q h U W d))) :
    HasCentralLaw (smallFamilyModel (fun i : ι => {σ : ι → Bool | σ i=true}))
      (smallFamilyEval f).rangeRestrict := by
  classical
  let T := fun d => Classical.choice (hlocal d)
  apply B.grid_formal_patching hlarge Q h U W hU hW he hdisjoint hcover f hspec
    (fun d => (T d).tests) (fun d => (T d).lawful) (fun d => (T d).margin)
    (fun d => (T d).predicates) (fun d => (T d).margin_resolved)
    (fun d => (T d).predicates_resolved) (fun d => (T d).controlled)
  intro d
  apply (T d).masked_actions (by omega) ?_ (B.gridPiece_supported (by omega) Q h U W hU hW d)
  change B.fullGeometricSector _ (Q none) (h none) (U none)=_
  rw [hconst,B.fullGeometricSector_whole]

end InitialCoverSystem
end LocalPatchTemplates

end SimpleAmenable
end
end

end OAI
