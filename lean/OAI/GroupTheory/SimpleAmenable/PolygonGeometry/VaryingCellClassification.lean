import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.LocalCoordinateClassifier
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.WindowClipping
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.ConcurrentGeometry

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section VaryingCellClassification

def axisDirection (j : Fin 2) : Fin 4 := Fin.castLE (by omega) j

@[simp] theorem integralCutForm_axis (a : ℕ) (j : Fin 2) (u : CutRing × CutRing) :
    integralCutForm a (axisDirection j) u=pointCoordinate u j := by
  fin_cases j <;> rfl

@[simp] theorem cutForm_axis (a : ℕ) (j : Fin 2) (z : ℝ × ℝ) :
    cutForm a (axisDirection j) z=realCoordinate z j := by
  fin_cases j <;> rfl

theorem slopeDirection_ne_axisDirection (d j : Fin 2) : slopeDirection d≠axisDirection j := by
  intro h
  have hh := congrArg Fin.val h
  simp only [slopeDirection,axisDirection,Fin.val_castLE] at hh
  omega

theorem varying_cell_classification {a : ℕ} (r : CutRing)
    (hr : 0<ordinary r ∧ ordinary r<1/2)
    (C : ConcurrentGeometry a r) (q : Fin 2 → ℤ)
    (hb : ∀ d, q d≤endpointLabel (-r) ∧ endpointLabel (-r)<q d+C.mesh)
    (he : ∀ d, q d≤endpointLabel r ∧ endpointLabel r<q d+C.mesh)
    (cell : Fin 2 → Fin C.mesh) (d j : Fin 2) (v : CutRing × CutRing) :
    (∃ b : Bool, clippedSlopePrimitive a r (slopeDirection d) ⊓ windowRectangle a C.mesh q cell=
      if b then windowRectangle a C.mesh q cell else ⊥) ∨
    (∃ b : Bool, spatialTranslate v (coordinatePrimitive a j) ⊓ windowRectangle a C.mesh q cell=
      if b then windowRectangle a C.mesh q cell else ⊥) ∨
    ∃ k : Fin 2 → ℤ, ∃ c : CutRing, ∃ positive : Bool,
      (∀ l, -ordinary r≤ordinary (windowCut C.mesh (q l) (cell l).castSucc)+(k l:ℝ) ∧
        ordinary (windowCut C.mesh (q l) (cell l).succ)+(k l:ℝ)≤ordinary r) ∧
      (∀ p ∈ (windowRectangle a C.mesh q cell).val,
        (p ∈ (spatialTranslate v (coordinatePrimitive a j)).val ↔
          if positive then ordinary c≤realCoordinate (windowPlanarLift q p) j
          else realCoordinate (windowPlanarLift q p) j<ordinary c)) ∧
      ∃ x y v' w : GenericSquare a,
        x ∈ (windowRectangle a C.mesh q cell).val ∧
        y ∈ (windowRectangle a C.mesh q cell).val ∧
        v' ∈ (windowRectangle a C.mesh q cell).val ∧
        w ∈ (windowRectangle a C.mesh q cell).val ∧
        cutForm a (slopeDirection d) (windowPlanarLift q x)≤
          ordinary (-integralCutForm a (slopeDirection d) ((k 0:CutRing),(k 1:CutRing))) ∧
        ordinary (-integralCutForm a (slopeDirection d) ((k 0:CutRing),(k 1:CutRing)))≤
          cutForm a (slopeDirection d) (windowPlanarLift q y) ∧
        cutForm a (axisDirection j) (windowPlanarLift q v')≤ordinary c ∧
        ordinary c≤cutForm a (axisDirection j) (windowPlanarLift q w) := by
  classical
  let W := windowRectangle a C.mesh q cell
  let U := clippedSlopePrimitive a r (slopeDirection d)
  let V := spatialTranslate v (coordinatePrimitive a j)
  have hconst (E : polygonAlgebra a) (b : Bool)
      (hh : ∀ p ∈ W.val, p ∈ E.val ↔ b=true) : E ⊓ W=if b then W else ⊥ := by
    apply Subtype.ext
    ext p
    cases b <;> simp only [Bool.false_eq_true,↓reduceIte] at hh ⊢
    · change (p ∈ E.val ∧ p ∈ W.val) ↔ False
      exact ⟨fun hp => (hh p hp.2).mp hp.1,False.elim⟩
    · change (p ∈ E.val ∧ p ∈ W.val) ↔ p ∈ W.val
      exact ⟨And.right,fun hp => ⟨(hh p hp).mpr trivial,hp⟩⟩
  by_cases hp : ∀ p ∈ W.val, p ∈ U.val
  · exact Or.inl ⟨true,hconst U true (fun p h => iff_of_true (hp p h) rfl)⟩
  by_cases hp' : ∀ p ∈ W.val, p ∉ U.val
  · exact Or.inl ⟨false,hconst U false (fun p h => iff_of_false (hp' p h) Bool.noConfusion)⟩
  by_cases hv : ∀ p ∈ W.val, p ∈ V.val
  · exact Or.inr (Or.inl ⟨true,hconst V true (fun p h => iff_of_true (hv p h) rfl)⟩)
  by_cases hv' : ∀ p ∈ W.val, p ∉ V.val
  · exact Or.inr (Or.inl ⟨false,hconst V false (fun p h => iff_of_false (hv' p h) Bool.noConfusion)⟩)
  push Not at hp hp' hv hv'
  obtain ⟨x,hx,hxn⟩ := hp
  obtain ⟨y,hy,hyp⟩ := hp'
  obtain ⟨v',hvv,hvn⟩ := hv
  obtain ⟨w,hw,hwp⟩ := hv'
  obtain hs | ⟨k,hk,hks⟩ := windowRectangle_slope_classifier r (slopeDirection d) hr C.mesh C.mesh_large q cell hb he
  · exact (hs y hy hyp).elim
  have hcx := le_of_lt (lt_of_not_ge (fun heq => hxn ((hks x hx).mpr heq)))
  have hcy := (hks y hy).mp hyp
  have hgap₁ : 200/(C.mesh:ℝ)<Real.goldenRatio-1 := by
    have he := C.mesh_small; have hp := C.positive; have hg := C.first_gap; linarith
  have hgap₂ : 200/(C.mesh:ℝ)<2-Real.goldenRatio := by
    have he := C.mesh_small; have hp := C.positive; have hg := C.second_gap; linarith
  obtain hc | hc | ⟨c,_hc₁,_hc₂,hc⟩ | ⟨c,_hc₁,_hc₂,hc⟩ :=
    windowRectangle_coordinate_classify C.mesh C.mesh_large hgap₁ hgap₂ q cell j v
  · exact (hvn (hc v' hvv)).elim
  · exact (hc w hw hwp).elim
  · refine Or.inr (Or.inr ⟨k,c,false,hk,by simpa only [Bool.false_eq_true,↓reduceIte] using hc,
      x,y,w,v',hx,hy,hw,hvv,hcx,hcy,?_,?_⟩)
    · simpa only [cutForm_axis] using ((hc w hw).mp hwp).le
    · simpa only [cutForm_axis] using (not_lt.mp (fun hh => hvn ((hc v' hvv).mpr hh)))
  · refine Or.inr (Or.inr ⟨k,c,true,hk,by simpa only [↓reduceIte] using hc,
      x,y,v',w,hx,hy,hvv,hw,hcx,hcy,?_,?_⟩)
    · simpa only [cutForm_axis] using (le_of_lt (lt_of_not_ge (fun hh => hvn ((hc v' hvv).mpr hh))))
    · simpa only [cutForm_axis] using (hc w hw).mp hwp

end VaryingCellClassification

end SimpleAmenable
end
end

end OAI
