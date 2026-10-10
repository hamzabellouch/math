import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.RectangularAtlas
import OAI.GroupTheory.SimpleAmenable.CentralCovers.GlobalSignControl

namespace OAI

open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement

theorem signQuadrant_bounds (s : CutRing) (hs : 0 ≤ ordinary s)
    (d : Fin 2) (positive : Bool) (j : Fin 2) :
    -ordinary s ≤ ordinary (signQuadrantLower s d positive j) ∧
    ordinary (signQuadrantUpper s d positive j) ≤ ordinary s := by
  cases positive <;> by_cases h : j=d <;>
    simp [signQuadrantLower,signQuadrantUpper,h] <;> linarith

namespace InitialCoverSystem
namespace RectangularAtlas
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    {B : InitialCoverSystem a r m hm M}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))] (A : B.RectangularAtlas)

theorem inactive_quadrant_action (hlarge : 20 ≤ m+1)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2)
    (d : Fin 2) (z z' : CutRing × CutRing) (positive : Bool)
    (hline : integralCutForm a (slopeDirection d) z=integralCutForm a (slopeDirection d) z')
    (L V : Fin 2 → CutRing) (hLV : ∀ j, ordinary (L j) ≤ ordinary (V j))
    (hz : ∀ j, -ordinary r ≤ ordinary (L j)-ordinary (pointCoordinate z j) ∧
      ordinary (V j)-ordinary (pointCoordinate z j) ≤ ordinary r)
    (hlo : ∀ j, ordinary (pointCoordinate z' j)+ordinary (signQuadrantLower A.radius d positive j) ≤ ordinary (L j))
    (hup : ∀ j, ordinary (V j) ≤ ordinary (pointCoordinate z' j)+ordinary (signQuadrantUpper A.radius d positive j))
    (n : ℕ) (q : Fin 2 → ℤ)
    (hW : ResolvedBy (fun i => (primitiveTests (a := a) (r := r)
      (coordinateWindowPrimitives n q) i).val) (coordinateRectangle a L V).val)
    (f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm))
    (hf : B.AlignedSmallSupported f)
    (hc : SmallControlled B.c f (B.windowSector (by omega) n (A.rectangles n) q (coordinateRectangle a L V)))
    (I : ControlAlphabet (Fin (m+1))) (s : UniversalExtension (alternatingGroup I.val))
    (t : BoundedRelationCover M (alternatingGenerator a r m hm)) (ht : t ∈ f.range) :
    A.slope (by omega) d z (universalMap (subtypeAlternatingHom I.val) s)*t*
      (A.slope (by omega) d z (universalMap (subtypeAlternatingHom I.val) s))⁻¹ =
    (if positive then B.c (subtypeAlternatingHom I.val (universalProjection (alternatingGroup I.val) s)) else 1)*t*
      (if positive then B.c (subtypeAlternatingHom I.val (universalProjection (alternatingGroup I.val) s)) else 1)⁻¹ := by
  have hbound (j : Fin 2) := signQuadrant_bounds A.radius A.radius_pos.le d positive j
  have hdiff (j : Fin 2) :
      |ordinary (L j)-ordinary (pointCoordinate z' j)| ≤ ordinary A.radius ∧
      |ordinary (V j)-ordinary (pointCoordinate z' j)| ≤ ordinary A.radius := by
    have hb := hbound j
    have hl := hlo j
    have hu := hup j
    have hlv := hLV j
    constructor <;> apply abs_le.mpr <;> constructor <;> linarith
  have hz' (j : Fin 2) : -ordinary r ≤ ordinary (L j)-ordinary (pointCoordinate z' j) ∧
      ordinary (V j)-ordinary (pointCoordinate z' j) ≤ ordinary r := by
    have hh := hdiff j
    have h₁ := (abs_le.mp hh.1).1
    have h₂ := (abs_le.mp hh.2).2
    constructor <;> linarith [A.radius_small]
  have he := A.slope_line_action hlarge hr d z z' hline L V hLV hz hz'
    (ordinary z'.1,ordinary z'.2) (by rw [cutForm_ordinary,hline])
    (fun j => by
      have hh := hdiff j
      have hh' : realCoordinate (ordinary z'.1,ordinary z'.2) j=ordinary (pointCoordinate z' j) := by
        fin_cases j <;> rfl
      rw [hh']
      constructor <;> linarith [A.radius_small]) n q hW f hf hc I s t ht
  rw [he]
  have hlab (j : Fin 2) :
      symmetricWindowStart A.radius j ≤ endpointLabel (signQuadrantLower A.radius d positive j) ∧
      endpointLabel (signQuadrantLower A.radius d positive j) <
        symmetricWindowStart A.radius j+symmetricWindowLength A.radius := by
    unfold signQuadrantLower
    split <;> split <;> first | exact (symmetricWindow_labels A.radius j).1 | exact (symmetricWindow_labels A.radius j).2.1
  have hvab (j : Fin 2) :
      symmetricWindowStart A.radius j ≤ endpointLabel (signQuadrantUpper A.radius d positive j) ∧
      endpointLabel (signQuadrantUpper A.radius d positive j) <
        symmetricWindowStart A.radius j+symmetricWindowLength A.radius := by
    unfold signQuadrantUpper
    split <;> split <;> first | exact (symmetricWindow_labels A.radius j).2.1 | exact (symmetricWindow_labels A.radius j).2.2
  have hside := signQuadrant_side (a := a) r A.radius hr
    ⟨A.radius_pos,by linarith [A.radius_small]⟩ d positive
  have hinc : coordinateRectangle a L V ≤ spatialTranslate z'
      (coordinateRectangle a (signQuadrantLower A.radius d positive) (signQuadrantUpper A.radius d positive)) := by
    rw [spatialTranslate_coordinateRectangle]
    apply coordinateRectangle_mono L V _ _
    · intro j; simpa only [map_add,pointCoordinate,add_comm] using hlo j
    · exact hLV
    · intro j; simpa only [map_add,pointCoordinate,add_comm] using hup j
    · intro j
      have hb := hbound j
      simp only [map_add,add_sub_add_right_eq_sub]
      linarith [A.radius_small,hr.2]
  have hc' := B.all_rectangle_control_to_sign hlarge A.rectangles _ _ A.u A.quadrants
    d z' positive _ _ hlab hvab hside n q _ hW hinc f hf hc
  have ht' := B.tangentSign_constant_action hlarge _ _ A.u A.quadrants d z' positive f hf hc' I s t ht
  have hs := B.tangentSign_eq (by omega) A.k _ A.p _ A.u A.u A.charts A.quadrants d z' true
  simpa only [slope,hs] using ht'

end RectangularAtlas
end InitialCoverSystem

end SimpleAmenable

end OAI
