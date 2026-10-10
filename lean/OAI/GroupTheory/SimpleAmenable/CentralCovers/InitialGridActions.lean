import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.FormalLaws
import OAI.GroupTheory.SimpleAmenable.CentralCovers.CoordinateTemplateControl
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.FinePatchAtlas

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section InitialGridActions
namespace InitialCoverSystem.PatchAtlas
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    {B : InitialCoverSystem a r m hm M}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))] (A : B.PatchAtlas)

theorem initial_grid_constant_action (hlarge : 20 ≤ m+1)
    (p : Fin 5 × (CutRing × CutRing)) (V : polygonAlgebra a)
    (hV : ResolvedBy (fun i => (primitiveTests (a := a) (r := r)
      (translatedTemplate (coordinateWindowPrimitives A.geometry.mesh (symmetricWindowStart r)) p.2) i).val) V.val)
    (b : Bool) (he : spatialTranslate p.2 (initialTest a r p.1) ⊓ V=if b then V else ⊥)
    (n : ℕ) (q : Fin 2 → ℤ) (W : polygonAlgebra a)
    (hW : ResolvedBy (fun i => (primitiveTests (a := a) (r := r)
      (coordinateWindowPrimitives n q) i).val) W.val)
    (hinc : W ≤ V)
    (f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm))
    (hf : B.AlignedSmallSupported f)
    (hc : SmallControlled B.c f (B.windowSector (by omega) n (A.rectangles.rectangles n) q W))
    (I : ControlAlphabet (Fin (m+1))) (s : UniversalExtension (alternatingGroup I.val))
    (x : BoundedRelationCover M (alternatingGenerator a r m hm)) (hx : x ∈ f.range) :
    A.primitiveStar (by omega) p (universalMap (subtypeAlternatingHom I.val) s)*x*
      (A.primitiveStar (by omega) p (universalMap (subtypeAlternatingHom I.val) s))⁻¹ =
    (if b then B.c (subtypeAlternatingHom I.val (universalProjection _ s)) else 1)*x*
      (if b then B.c (subtypeAlternatingHom I.val (universalProjection _ s)) else 1)⁻¹ := by
  let P := translatedTemplate (initialPatchPrimitives r A.geometry.mesh) p.2
  let h := fun J (_ : J.card ≤ 15) c hc => A.initial p.2 J c hc
  have hVp : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) P i).val) V.val :=
    fun x y he => hV x y (fun i => he (Sum.inr i))
  have hU : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) P i).val)
      (spatialTranslate p.2 (initialTest a r p.1)).val := by
    intro x y he
    simpa only [P,primitiveTests,primitiveFamilyTests,translatedTemplate,initialPatchPrimitives,
      Sum.elim_inl,add_zero] using he (Sum.inl p.1)
  have hctrl : SmallControlled B.c f (B.fullGeometricSector (by omega) P h V) := by
    exact B.coordinate_control_to_template hlarge A.rectangles.rectangles P h Prod.fst
      (fun i => p.2+(coordinateWindowPrimitives A.geometry.mesh (symmetricWindowStart r) i).2)
      Sum.inr rfl V hV n q W hW hinc f hf hc
  exact B.cell_constant_action hlarge P h _ V hU hVp b he f hf hctrl I s x hx

theorem primitiveStar_slope (hlarge : 15 < m+1) (d : Fin 2) (v : CutRing × CutRing) :
    A.primitiveStar hlarge (slopeTestIndex d,v)=A.rectangles.slope hlarge d v := by
  symm
  unfold primitiveStar
  rw [initialTest_slope]
  apply A.rectangles.slope_chart_eq hlarge _ _ (Sum.inl (slopeTestIndex d)) d v
  simp [translatedTemplate,initialPatchPrimitives]

end InitialCoverSystem.PatchAtlas
end InitialGridActions

section LiftedFarGridActions
namespace InitialCoverSystem.PatchAtlas
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    {B : InitialCoverSystem a r m hm M}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))] (A : B.PatchAtlas)

theorem far_grid_action (hlarge : 20 ≤ m+1)
    (hr : 0<ordinary r ∧ ordinary r<1/2) (d : Fin 2) (v : CutRing × CutRing)
    (cell : Fin 2 → Fin A.geometry.mesh) (k : Fin 2 → ℤ)
    (hk : ∀ e, -ordinary r ≤ ordinary (windowCut A.geometry.mesh
      (symmetricWindowStart r e) (cell e).castSucc)+(k e:ℝ) ∧
      ordinary (windowCut A.geometry.mesh (symmetricWindowStart r e) (cell e).succ)+(k e:ℝ) ≤ ordinary r)
    (z : ℝ × ℝ) (hz : ∀ e,
      ordinary (windowCut A.geometry.mesh (symmetricWindowStart r e) (cell e).castSucc) ≤ realCoordinate z e ∧
      realCoordinate z e ≤ ordinary (windowCut A.geometry.mesh (symmetricWindowStart r e) (cell e).succ))
    (hfar : (1+|ordinary (cutTau^a)|)*(200/(A.geometry.mesh:ℝ)) <
      |cutForm a (slopeDirection d) z+cutForm a (slopeDirection d) ((k 0:ℝ),(k 1:ℝ))|)
    (n : ℕ) (q : Fin 2 → ℤ) (W : polygonAlgebra a)
    (hW : ResolvedBy (fun i => (primitiveTests (a := a) (r := r)
      (coordinateWindowPrimitives n q) i).val) W.val)
    (hinc : W ≤ spatialTranslate v (windowRectangle a A.geometry.mesh (symmetricWindowStart r) cell))
    (f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm))
    (hf : B.AlignedSmallSupported f)
    (hc : SmallControlled B.c f (B.windowSector (by omega) n (A.rectangles.rectangles n) q W))
    (I : ControlAlphabet (Fin (m+1))) (s : UniversalExtension (alternatingGroup I.val))
    (x : BoundedRelationCover M (alternatingGenerator a r m hm)) (hx : x ∈ f.range) :
    A.rectangles.slope (by omega) d v (universalMap (subtypeAlternatingHom I.val) s)*x*
      (A.rectangles.slope (by omega) d v (universalMap (subtypeAlternatingHom I.val) s))⁻¹ =
    (if 0 ≤ cutForm a (slopeDirection d) z+cutForm a (slopeDirection d) ((k 0:ℝ),(k 1:ℝ))
      then B.c (subtypeAlternatingHom I.val (universalProjection _ s)) else 1)*x*
      (if 0 ≤ cutForm a (slopeDirection d) z+cutForm a (slopeDirection d) ((k 0:ℝ),(k 1:ℝ))
      then B.c (subtypeAlternatingHom I.val (universalProjection _ s)) else 1)⁻¹ := by
  classical
  let b : Bool := decide (0 ≤ cutForm a (slopeDirection d) z+
    cutForm a (slopeDirection d) ((k 0:ℝ),(k 1:ℝ)))
  have hres := translatedTemplate_resolved (a := a) (r := r)
    (coordinateWindowPrimitives A.geometry.mesh (symmetricWindowStart r))
    (windowRectangle a A.geometry.mesh (symmetricWindowStart r) cell)
    (windowRectangle_resolved A.geometry.mesh (by have := A.geometry.mesh_large; omega) _ cell) v
  have he : spatialTranslate v (initialTest a r (slopeTestIndex d)) ⊓
      spatialTranslate v (windowRectangle a A.geometry.mesh (symmetricWindowStart r) cell)=
      if b then spatialTranslate v (windowRectangle a A.geometry.mesh (symmetricWindowStart r) cell) else ⊥ := by
    rw [initialTest_slope,← spatialTranslate_inter,
      windowRectangle_far_clipped r (slopeDirection d) hr A.geometry.mesh
        (by have := A.geometry.mesh_large; omega) _ cell k hk z hz hfar]
    simp only [b,decide_eq_true_eq]
    split_ifs <;> rfl
  have hh := A.initial_grid_constant_action hlarge (slopeTestIndex d,v) _ hres b he
    n q W hW hinc f hf hc I s x hx
  rw [A.primitiveStar_slope] at hh
  simpa only [b,decide_eq_true_eq] using hh

theorem exterior_grid_action (hlarge : 20 ≤ m+1)
    (hr : 0<ordinary r ∧ ordinary r<1/2) (d : Fin 2) (v : CutRing × CutRing)
    (cell : Fin 2 → Fin A.geometry.mesh)
    (hout : Disjoint (windowRectangle a A.geometry.mesh (symmetricWindowStart r) cell)
      (coordinateRectangle a (fun _ => -r) (fun _ => r)))
    (n : ℕ) (q : Fin 2 → ℤ) (W : polygonAlgebra a)
    (hW : ResolvedBy (fun i => (primitiveTests (a := a) (r := r)
      (coordinateWindowPrimitives n q) i).val) W.val)
    (hinc : W ≤ spatialTranslate v (windowRectangle a A.geometry.mesh (symmetricWindowStart r) cell))
    (f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm))
    (hf : B.AlignedSmallSupported f)
    (hc : SmallControlled B.c f (B.windowSector (by omega) n (A.rectangles.rectangles n) q W))
    (I : ControlAlphabet (Fin (m+1))) (s : UniversalExtension (alternatingGroup I.val))
    (x : BoundedRelationCover M (alternatingGenerator a r m hm)) (hx : x ∈ f.range) :
    Commute (A.rectangles.slope (by omega) d v (universalMap (subtypeAlternatingHom I.val) s)) x := by
  have hres := translatedTemplate_resolved (a := a) (r := r)
    (coordinateWindowPrimitives A.geometry.mesh (symmetricWindowStart r))
    (windowRectangle a A.geometry.mesh (symmetricWindowStart r) cell)
    (windowRectangle_resolved A.geometry.mesh (by have := A.geometry.mesh_large; omega) _ cell) v
  have hd : Disjoint (clippedSlopePrimitive a r (slopeDirection d))
      (windowRectangle a A.geometry.mesh (symmetricWindowStart r) cell) :=
    hout.symm.mono_left (clippedSlope_le_box r (slopeDirection d) hr)
  have he : spatialTranslate v (initialTest a r (slopeTestIndex d)) ⊓
      spatialTranslate v (windowRectangle a A.geometry.mesh (symmetricWindowStart r) cell)=
      if false then spatialTranslate v (windowRectangle a A.geometry.mesh (symmetricWindowStart r) cell) else ⊥ := by
    rw [initialTest_slope,← spatialTranslate_inter,disjoint_iff.mp hd]
    rfl
  have hh := A.initial_grid_constant_action hlarge (slopeTestIndex d,v) _ hres false he
    n q W hW hinc f hf hc I s x hx
  rw [A.primitiveStar_slope] at hh
  simp only [Bool.false_eq_true,↓reduceIte,inv_one,one_mul,mul_one] at hh
  change _ * x = x * _
  have hh' := congrArg (fun y => y*A.rectangles.slope (by omega) d v
    (universalMap (subtypeAlternatingHom I.val) s)) hh
  simpa only [mul_assoc,inv_mul_cancel,mul_one] using hh'

end InitialCoverSystem.PatchAtlas
end LiftedFarGridActions

end SimpleAmenable
end
end

end OAI
