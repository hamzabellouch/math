import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.ConcurrentGeometry
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.InactiveNeighborhoodActions

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section SelectedInwardActions
namespace InitialCoverSystem.PatchAtlas
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    {B : InitialCoverSystem a r m hm M}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (A : B.PatchAtlas) {ι : Type*}

theorem selected_active_slope_actions
    (hlarge : 20 ≤ m+1) (hr : 0<ordinary r ∧ ordinary r<1/2)
    {j : ι → Fin 4} {c : ι → CutRing} {z : ℝ × ℝ}
    (T : A.geometry.InwardChart j c z) (i : ι)
    (hi : cutForm a (j i) z=ordinary (c i))
    (d : Fin 2) (hd : j i=slopeDirection d) (v : CutRing × CutRing)
    (hv : integralCutForm a (slopeDirection d) v=c i)
    (L V : Fin 2 → CutRing)
    (hLV : ∀ k, ordinary (L k)≤ordinary (V k))
    (hclip : ∀ k, -ordinary r≤ordinary (L k)-ordinary (pointCoordinate v k) ∧
      ordinary (V k)-ordinary (pointCoordinate v k)≤ordinary r)
    (hnear : ∀ k, |ordinary (L k)-realCoordinate z k|<A.geometry.epsilon/2 ∧
      |ordinary (V k)-realCoordinate z k|<A.geometry.epsilon/2)
    (n : ℕ) (q : Fin 2 → ℤ)
    (hW : ResolvedBy (fun e => (primitiveTests (a := a) (r := r)
      (coordinateWindowPrimitives n q) e).val) (coordinateRectangle a L V).val)
    (f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm))
    (hf : B.AlignedSmallSupported f)
    (hc : SmallControlled B.c f (B.windowSector (by omega) n (A.rectangles.rectangles n) q
      (coordinateRectangle a L V)))
    (I : ControlAlphabet (Fin (m+1))) (s : UniversalExtension (alternatingGroup I.val))
    (b : BoundedRelationCover M (alternatingGenerator a r m hm)) (hb : b ∈ f.range) :
      A.rectangles.slope (by omega) d v (universalMap (subtypeAlternatingHom I.val) s)*b*
        (A.rectangles.slope (by omega) d v (universalMap (subtypeAlternatingHom I.val) s))⁻¹ =
      A.rectangles.slope (by omega) d (T.offset+A.geometry.anchors T.vertex (j i))
          (universalMap (subtypeAlternatingHom I.val) s)*b*
        (A.rectangles.slope (by omega) d (T.offset+A.geometry.anchors T.vertex (j i))
          (universalMap (subtypeAlternatingHom I.val) s))⁻¹ := by
  have hLdist : dist (ordinary (L 0),ordinary (L 1)) z < A.geometry.epsilon/2 := by
    rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq,max_lt_iff]
    exact ⟨(hnear 0).1,(hnear 1).1⟩
  have hVdist : dist (ordinary (V 0),ordinary (V 1)) z < A.geometry.epsilon/2 := by
    rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq,max_lt_iff]
    exact ⟨(hnear 0).2,(hnear 1).2⟩
  have hclip' : ∀ k, -ordinary r ≤ ordinary (L k)-ordinary (pointCoordinate (T.offset+A.geometry.anchors T.vertex (j i)) k) ∧
      ordinary (V k)-ordinary (pointCoordinate (T.offset+A.geometry.anchors T.vertex (j i)) k) ≤ ordinary r := by
    intro k
    have hL := (T.active_bound i hi) (ordinary (L 0),ordinary (L 1))
      (fun l => (T.neighborhood _ hLdist l).imp le_of_lt le_of_lt) k
    have hV := (T.active_bound i hi) (ordinary (V 0),ordinary (V 1))
      (fun l => (T.neighborhood _ hVdist l).imp le_of_lt le_of_lt) k
    have heL : realCoordinate (ordinary (L 0),ordinary (L 1)) k=ordinary (L k) := by fin_cases k <;> rfl
    have heV : realCoordinate (ordinary (V 0),ordinary (V 1)) k=ordinary (V k) := by fin_cases k <;> rfl
    rw [heL] at hL
    rw [heV] at hV
    have hL' := (abs_lt.mp hL).1
    have hV' := (abs_lt.mp hV).2
    have hrad := A.geometry.radius
    have hpos := A.geometry.positive
    constructor <;> linarith
  have hline : integralCutForm a (slopeDirection d) v=
      integralCutForm a (slopeDirection d) (T.offset+A.geometry.anchors T.vertex (j i)) := by
    rw [hv,← hd,(T.active_anchor i hi)]
  have hz : cutForm a (slopeDirection d) z=ordinary (integralCutForm a (slopeDirection d) v) := by
    rw [hv,← hd]; exact hi
  have hnear' : ∀ k, |ordinary (L k)-realCoordinate z k| ≤ ordinary r/4 ∧
      |ordinary (V k)-realCoordinate z k| ≤ ordinary r/4 := by
    intro k
    have hh := hnear k
    have hrad := A.geometry.radius
    have hpos := A.geometry.positive
    constructor <;> linarith
  exact A.rectangles.slope_line_action hlarge hr d v (T.offset+A.geometry.anchors T.vertex (j i)) hline L V hLV
    hclip hclip' z hz hnear' n q hW f hf hc I s b hb

end InitialCoverSystem.PatchAtlas
end SelectedInwardActions

end SimpleAmenable
end
end

end OAI
