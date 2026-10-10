import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.LocalChartDecisions
import OAI.GroupTheory.SimpleAmenable.CentralCovers.ClippedLineSlideAction

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section RectangularAtlas
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

structure RectangularAtlas where
  k : ℕ
  p : Fin 2 → ℤ
  u : CutRing
  v : CutRing
  inverse : u*v=1
  short : 4*(1+|ordinary (cutTau^a)|)*(|ordinary u|+|ordinary (cutTau*u)|) ≤ ordinary r
  labels : ∀ d e j,
    (p j ≤ endpointLabel (clippingOverlapLower r (tangentOffset a d (signedShortSteps u e)) j) ∧
     endpointLabel (clippingOverlapLower r (tangentOffset a d (signedShortSteps u e)) j) < p j+k) ∧
    (p j ≤ endpointLabel (clippingOverlapUpper r (tangentOffset a d (signedShortSteps u e)) j) ∧
     endpointLabel (clippingOverlapUpper r (tangentOffset a d (signedShortSteps u e)) j) < p j+k)
  rectangles : ∀ n, B.CoordinateWindowLaw n
  charts : B.TangentChartLaws k p u
  radius : CutRing
  radius_pos : 0 < ordinary radius
  radius_small : ordinary radius < ordinary r/8
  quadrants : B.TangentChartLaws (symmetricWindowLength radius) (symmetricWindowStart radius) u

namespace RectangularAtlas
variable {B} (A : B.RectangularAtlas)

noncomputable def slope (hlarge : 15 < m+1) (d : Fin 2) (z : CutRing × CutRing) :
    TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm) :=
  B.tangentSign hlarge A.k A.p A.u A.charts d z true

theorem slope_line_action (hlarge : 20 ≤ m+1)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2)
    (d : Fin 2) (z z' : CutRing × CutRing)
    (hline : integralCutForm a (slopeDirection d) z=integralCutForm a (slopeDirection d) z')
    (L V : Fin 2 → CutRing) (hLV : ∀ j, ordinary (L j) ≤ ordinary (V j))
    (hz : ∀ j, -ordinary r ≤ ordinary (L j)-ordinary (pointCoordinate z j) ∧
      ordinary (V j)-ordinary (pointCoordinate z j) ≤ ordinary r)
    (hz' : ∀ j, -ordinary r ≤ ordinary (L j)-ordinary (pointCoordinate z' j) ∧
      ordinary (V j)-ordinary (pointCoordinate z' j) ≤ ordinary r)
    (x : ℝ × ℝ) (hx : cutForm a (slopeDirection d) x=ordinary (integralCutForm a (slopeDirection d) z))
    (hnear : ∀ j, |ordinary (L j)-realCoordinate x j| ≤ ordinary r/4 ∧
      |ordinary (V j)-realCoordinate x j| ≤ ordinary r/4)
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
    A.slope (by omega) d z' (universalMap (subtypeAlternatingHom I.val) s)*t*
      (A.slope (by omega) d z' (universalMap (subtypeAlternatingHom I.val) s))⁻¹ := by
  obtain ⟨w,rfl⟩ := slope_same_intercept a d z z' hline
  obtain ⟨c,hc'⟩ := real_slope_parameter a d z x hx
  exact B.tangent_line_slide hlarge hr A.rectangles A.k A.p A.u A.v A.inverse A.charts A.short
    A.labels d z w L V hLV hz hz' c (by simpa only [← hc'] using hnear) n q hW f hf hc I s t ht

end RectangularAtlas
end InitialCoverSystem

theorem rectangularAtlas_eventually {a m : ℕ} {r : CutRing} {hm : 2 ≤ m}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))] (hlarge : 20 ≤ m+1)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2)
    (hSlope : 8000 < ordinary (cutTau^a)) (hconj : |conjugate (cutTau^a)| < 1/1000) :
    ∃ L : ℕ, ∀ M : ℕ, L ≤ M → ∀ B : InitialCoverSystem a r m hm M,
      Nonempty B.RectangularAtlas := by
  obtain ⟨s,u,v,hs,hsr,huv,hshort⟩ := exists_symmetric_short_chart a r hr.1
  obtain ⟨k,p,hp⟩ := exists_full_overlap_window a r u
  obtain ⟨s₁,hs₁,hs₁'⟩ := exists_cut_between (by linarith : (0:ℝ) < ordinary r/8)
  obtain ⟨L₁,hL₁⟩ := coordinate_all_eventually (hm := hm) hlarge hr hSlope hconj
  obtain ⟨L₂,hL₂⟩ := tangentChartTables_eventually (hm := hm) hr (by omega) k p u
  obtain ⟨L₃,hL₃⟩ := tangentChartTables_eventually (hm := hm) hr (by omega)
    (symmetricWindowLength s₁) (symmetricWindowStart s₁) u
  refine ⟨L₁+L₂+L₃,fun M hM B => ⟨⟨k,p,u,v,huv,?_,hp,hL₁ M (by omega) B,?_,s₁,hs₁,hs₁',?_⟩⟩⟩
  · nlinarith
  · intro d e z I _ b hb
    exact hL₂ M (by omega) B d e z I b hb
  · intro d e z I _ b hb
    exact hL₃ M (by omega) B d e z I b hb

end RectangularAtlas

end SimpleAmenable
end
end

end OAI
