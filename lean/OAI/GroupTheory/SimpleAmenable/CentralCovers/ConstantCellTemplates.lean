import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.GlobalTangentChain
import OAI.GroupTheory.SimpleAmenable.CentralCovers.CrossingCellActions

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section ConstantCellTemplates
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) {J : Type*} {κ : Type} [Finite κ]
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem constant_cell_template (hlarge : 20 ≤ m+1)
    (F : Option (Fin 2) → TrackStar (Fin (m+1)) →*
      BoundedRelationCover M (alternatingGenerator a r m hm))
    (f : J → TrackStar (Fin (m+1)) →*
      BoundedRelationCover M (alternatingGenerator a r m hm))
    (P : Fin 2 → κ → Fin 5 × (CutRing × CutRing))
    (h : ∀ i I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb (P i))
    (U : Fin 2 → polygonAlgebra a) (W : polygonAlgebra a)
    (hF : ∀ i, F (some i)=B.fullGeometricSector (by omega) (P i) (h i) (U i))
    (hU : ∀ i, ResolvedBy (fun j => (primitiveTests (a := a) (r := r) (P i) j).val) (U i).val)
    (hW : ∀ i, ResolvedBy (fun j => (primitiveTests (a := a) (r := r) (P i) j).val) W.val)
    (hf : ∀ j, B.AlignedSmallSupported (f j))
    (hc : ∀ i j, SmallControlled B.c (f j) (B.fullGeometricSector (by omega) (P i) (h i) W))
    (i i' : Fin 2) (hne : i≠i') (positive : Bool)
    (he : U i ⊓ W=if positive then W else ⊥) :
    Nonempty (B.LocalPatchTemplate (by omega) F f) := by
  classical
  let V : polygonAlgebra a := if positive then wholePolygon a else ⊥
  let R : Fin 2 → polygonAlgebra a := fun j => if j=i then V else U i'
  refine ⟨{ index := κ
            tests := P i'
            lawful := h i'
            margin := W
            predicates := R
            margin_resolved := hW i'
            predicates_resolved := ?_
            controlled := hc i'
            action := ?_ }⟩
  · intro j
    by_cases hj : j=i
    · simp only [R,hj,↓reduceIte]
      cases positive <;> exact fun _ _ _ => Iff.rfl
    · simpa only [R,hj,↓reduceIte] using hU i'
  · intro j I s l x hx
    let I' : ControlAlphabet (Fin (m+1)) := ⟨I.val,by rw [I.property.2]; omega⟩
    by_cases hj : j=i
    · subst j
      rw [hF]
      have hh := B.cell_constant_action hlarge (P i) (h i) (U i) W (hU i) (hW i)
        positive he (f l) (hf l) (hc i l) I' s x hx
      have hπ := DFunLike.congr_fun (universalMap_spec (subtypeAlternatingHom I.val)) s
      simp only [MonoidHom.comp_apply] at hπ
      cases positive <;>
        simpa only [R,V,Bool.false_eq_true,↓reduceIte,B.fullGeometricSector_whole,B.fullGeometricSector_bot,
          MonoidHom.comp_apply,MonoidHom.one_apply,hπ] using hh
    · have hj' : j=i' := by
        fin_cases i <;> fin_cases i' <;> fin_cases j <;> simp_all
      subst j
      simp only [R,Ne.symm hne,↓reduceIte,hF]

end InitialCoverSystem
end ConstantCellTemplates

section SlopeCoordinateCellTemplate
namespace InitialCoverSystem.PatchAtlas
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    {B : InitialCoverSystem a r m hm M}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (A : B.PatchAtlas)

theorem slope_coordinate_cell_template {κ : Type} [Finite κ] {J : Type*}
    (hlarge : 20 ≤ m+1) (hr : 0<ordinary r ∧ ordinary r<1/2) (ha : 0<a)
    (d j : Fin 2) (v : CutRing × CutRing)
    (P : Fin 2 → κ → Fin 5 × (CutRing × CutRing))
    (h : ∀ i I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb (P i))
    (i₀ i₁ : κ) (hP : P 0 i₀=(slopeTestIndex d,0)) (hQ : P 1 i₁=(coordinateTestIndex j,v))
    (F : Option (Fin 2) → TrackStar (Fin (m+1)) →*
      BoundedRelationCover M (alternatingGenerator a r m hm))
    (f : J → TrackStar (Fin (m+1)) →*
      BoundedRelationCover M (alternatingGenerator a r m hm))
    (hF : ∀ i, F (some i)=B.fullGeometricSector (by omega) (P i) (h i)
      (![clippedSlopePrimitive a r (slopeDirection d),spatialTranslate v (coordinatePrimitive a j)] i))
    (q : Fin 2 → ℤ) (cell : Fin 2 → Fin A.geometry.mesh)
    (hb : ∀ k, q k ≤ endpointLabel (-r) ∧ endpointLabel (-r)<q k+A.geometry.mesh)
    (he : ∀ k, q k ≤ endpointLabel r ∧ endpointLabel r<q k+A.geometry.mesh)
    (hW : ∀ i, ResolvedBy (fun s => (InitialCoverSystem.primitiveTests (a := a) (r := r) (P i) s).val)
      (windowRectangle a A.geometry.mesh q cell).val)
    (hcoherent : ∀ i, B.fullGeometricSector (by omega) (P i) (h i)
      (windowRectangle a A.geometry.mesh q cell)=B.windowSector (by omega) A.geometry.mesh
        (A.rectangles.rectangles A.geometry.mesh) q (windowRectangle a A.geometry.mesh q cell))
    (hf : ∀ l, B.AlignedSmallSupported (f l))
    (hcontrol : ∀ l, SmallControlled B.c (f l) (B.windowSector (by omega) A.geometry.mesh
      (A.rectangles.rectangles A.geometry.mesh) q (windowRectangle a A.geometry.mesh q cell))) :
    Nonempty (B.LocalPatchTemplate (by omega) F f) := by
  let U : Fin 2 → polygonAlgebra a :=
    ![clippedSlopePrimitive a r (slopeDirection d),spatialTranslate v (coordinatePrimitive a j)]
  have hU : ∀ i, ResolvedBy (fun s => (InitialCoverSystem.primitiveTests (a := a) (r := r) (P i) s).val) (U i).val := by
    intro i x y hxy
    fin_cases i
    · change x ∈ (clippedSlopePrimitive a r (slopeDirection d)).val ↔
        y ∈ (clippedSlopePrimitive a r (slopeDirection d)).val
      have hh := hxy i₀
      change x ∈ (spatialTranslate (P 0 i₀).2 (initialTest a r (P 0 i₀).1)).val ↔
        y ∈ (spatialTranslate (P 0 i₀).2 (initialTest a r (P 0 i₀).1)).val at hh
      simpa only [hP,initialTest_slope,spatialTranslate_zero] using hh
    · change x ∈ (spatialTranslate v (coordinatePrimitive a j)).val ↔
        y ∈ (spatialTranslate v (coordinatePrimitive a j)).val
      have hh := hxy i₁
      change x ∈ (spatialTranslate (P 1 i₁).2 (initialTest a r (P 1 i₁).1)).val ↔
        y ∈ (spatialTranslate (P 1 i₁).2 (initialTest a r (P 1 i₁).1)).val at hh
      simpa only [hQ,initialTest_coordinate] using hh
  have hctrl : ∀ i l, SmallControlled B.c (f l) (B.fullGeometricSector (by omega) (P i) (h i)
      (windowRectangle a A.geometry.mesh q cell)) := by
    intro i l
    rw [hcoherent i]
    exact hcontrol l
  obtain ⟨b,hb'⟩ | ⟨b,hb'⟩ | ⟨k,c,positive,hk,hc,x,y,v',w,hx,hy,hv,hw,hcx,hcy,hdv,hdw⟩ :=
    varying_cell_classification r hr A.geometry q hb he cell d j v
  · exact B.constant_cell_template hlarge F f P h U _ hF hU hW hf hctrl 0 1 (by decide) b hb'
  · exact B.constant_cell_template hlarge F f P h U _ hF hU hW hf hctrl 1 0 (by decide) b hb'
  · obtain ⟨t,u,hinc,hact⟩ := A.crossing_cell_actions hlarge hr ha (P 0) (P 1) (h 0) (h 1)
      i₀ i₁ d j v hP hQ q cell k c positive hk hc x y v' w hx hy hv hw hcx hcy hdv hdw
    let R : Fin 2 → polygonAlgebra a := ![
      spatialTranslate (u+A.geometry.anchors t (slopeDirection d)) (clippedSlopePrimitive a r (slopeDirection d)),
      if positive then spatialTranslate (u+A.geometry.anchors t (axisDirection j)) (coordinatePrimitive a j)
        else (spatialTranslate (u+A.geometry.anchors t (axisDirection j)) (coordinatePrimitive a j))ᶜ]
    have hrMargin : ResolvedBy (fun s => (InitialCoverSystem.primitiveTests (a := a) (r := r)
        (A.concurrentPrimitives t u) s).val) (A.margin t u).val := by
      intro x y hh
      exact translatedTemplate_resolved (Sum.elim
        (fun j : Fin 4 => (⟨j.val+1,by omega⟩,A.geometry.anchors t j))
        (coordinateWindowPrimitives A.geometry.window A.geometry.start))
        (coordinateRectangle a (A.geometry.margins t).lower (A.geometry.margins t).upper)
        (fun x y hh => A.geometry.margin_resolved t x y (fun i => hh (Sum.inr i))) u x y hh
    have hrc : ∀ l, SmallControlled B.c (f l)
        (B.fullGeometricSector (by omega) (A.concurrentPrimitives t u) (A.concurrentLaw t u) (A.margin t u)) := by
      intro l
      apply B.all_rectangle_control_to_template hlarge A.rectangles.rectangles A.geometry.window
        A.geometry.start u (A.concurrentPrimitives t u) (A.concurrentLaw t u) Sum.inr (fun _ => rfl)
        _ (A.geometry.margin_resolved t)
        (translated_rectangle_window A.geometry.start u _ _
          (fun j => (A.geometry.labels t j).1) (fun j => (A.geometry.labels t j).2))
        A.geometry.mesh q _
        (windowRectangle_resolved A.geometry.mesh (by have hh := A.geometry.mesh_large; omega) q cell)
        hinc (f l) (hf l) (hcontrol l)
    refine ⟨{ index := Sum (Fin 4) (Fin 2 × Fin (A.geometry.window-1))
              tests := A.concurrentPrimitives t u
              lawful := A.concurrentLaw t u
              margin := A.margin t u
              predicates := R
              margin_resolved := hrMargin
              predicates_resolved := ?_
              controlled := hrc
              action := ?_ }⟩
    · intro l x y hh
      fin_cases l
      · change x ∈ (spatialTranslate (u+A.geometry.anchors t (slopeDirection d))
            (clippedSlopePrimitive a r (slopeDirection d))).val ↔
          y ∈ (spatialTranslate (u+A.geometry.anchors t (slopeDirection d))
            (clippedSlopePrimitive a r (slopeDirection d))).val
        have hs := hh (Sum.inl (slopeDirection d))
        change x ∈ (spatialTranslate (u+A.geometry.anchors t (slopeDirection d))
            (initialTest a r (slopeTestIndex d))).val ↔
          y ∈ (spatialTranslate (u+A.geometry.anchors t (slopeDirection d))
            (initialTest a r (slopeTestIndex d))).val at hs
        simpa only [initialTest_slope] using hs
      · have hs := hh (Sum.inl (axisDirection j))
        change x ∈ (spatialTranslate (u+A.geometry.anchors t (axisDirection j))
            (initialTest a r (coordinateTestIndex j))).val ↔
          y ∈ (spatialTranslate (u+A.geometry.anchors t (axisDirection j))
            (initialTest a r (coordinateTestIndex j))).val at hs
        rw [initialTest_coordinate] at hs
        cases positive <;> change _ ↔ _
        · exact not_congr hs
        · exact hs
    · intro l I s l' x hx'
      let I' : ControlAlphabet (Fin (m+1)) := ⟨I.val,by rw [I.property.2]; omega⟩
      have hh := hact (f l') (hf l') (hcontrol l') I' s x hx'
      rw [hF]
      fin_cases l
      · exact hh.1
      · exact hh.2

end InitialCoverSystem.PatchAtlas
end SlopeCoordinateCellTemplate

end SimpleAmenable
end
end

end OAI
