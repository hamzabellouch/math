import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.IntervalTangentConnectivity
import OAI.GroupTheory.SimpleAmenable.Homology.ClippedLineSlide
import OAI.GroupTheory.SimpleAmenable.Homology.GlobalTangentChain

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section ClippedLineSlideAction
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem tangent_interval_edge_action (hlarge : 20 ≤ m+1)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2)
    (g : ∀ n, B.CoordinateWindowLaw n)
    (k : ℕ) (p : Fin 2 → ℤ) (u : CutRing) (h : B.TangentChartLaws k p u)
    (d : Fin 2)
    (hsteps : ∀ e j, |ordinary (pointCoordinate (tangentOffset a d (signedShortSteps u e)) j)| ≤ 2*ordinary r)
    (hlabels : ∀ e j,
      (p j ≤ endpointLabel (clippingOverlapLower r (tangentOffset a d (signedShortSteps u e)) j) ∧
       endpointLabel (clippingOverlapLower r (tangentOffset a d (signedShortSteps u e)) j) < p j+k) ∧
      (p j ≤ endpointLabel (clippingOverlapUpper r (tangentOffset a d (signedShortSteps u e)) j) ∧
       endpointLabel (clippingOverlapUpper r (tangentOffset a d (signedShortSteps u e)) j) < p j+k))
    (z : CutRing × CutRing) (L V : Fin 2 → CutRing)
    (hLV : ∀ j, ordinary (L j) ≤ ordinary (V j))
    (A C : ℝ) (x y : CutRing) (hstep : TangentIntervalStep u A C x y)
    (hcenters : ∀ t : CutRing, A ≤ ordinary t → ordinary t ≤ C → ∀ j,
      -ordinary r ≤ ordinary (L j)-ordinary (pointCoordinate (z+tangentOffset a d t) j) ∧
      ordinary (V j)-ordinary (pointCoordinate (z+tangentOffset a d t) j) ≤ ordinary r)
    (n : ℕ) (q : Fin 2 → ℤ)
    (hW : ResolvedBy (fun i => (primitiveTests (a := a) (r := r)
      (coordinateWindowPrimitives n q) i).val) (coordinateRectangle a L V).val)
    (f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm))
    (hf : B.AlignedSmallSupported f)
    (hc : SmallControlled B.c f (B.windowSector (by omega) n (g n) q (coordinateRectangle a L V)))
    (I : ControlAlphabet (Fin (m+1))) (s : UniversalExtension (alternatingGroup I.val))
    (t : BoundedRelationCover M (alternatingGenerator a r m hm)) (ht : t ∈ f.range) :
    B.tangentSign (by omega) k p u h d (z+tangentOffset a d x) true
        (universalMap (subtypeAlternatingHom I.val) s)*t*
      (B.tangentSign (by omega) k p u h d (z+tangentOffset a d x) true
        (universalMap (subtypeAlternatingHom I.val) s))⁻¹ =
    B.tangentSign (by omega) k p u h d (z+tangentOffset a d y) true
        (universalMap (subtypeAlternatingHom I.val) s)*t*
      (B.tangentSign (by omega) k p u h d (z+tangentOffset a d y) true
        (universalMap (subtypeAlternatingHom I.val) s))⁻¹ := by
  obtain ⟨e,he⟩ := tangentIntervalStep_index hstep
  have hy := hcenters x hstep.1 hstep.2.1
  have hy' := hcenters y hstep.2.2.1 hstep.2.2.2.1
  have hcenter : z+tangentOffset a d y = (z+tangentOffset a d x)+tangentOffset a d (signedShortSteps u e) := by
    rw [he,tangentOffset_add,add_assoc]
  have hb := clippingOverlap_bounds r (tangentOffset a d (signedShortSteps u e)) hr (hsteps e)
  have hinc := coordinateRectangle_in_clippingOverlap (a := a) r hr
    (z+tangentOffset a d x) (tangentOffset a d (signedShortSteps u e)) L V hLV (hsteps e) hy
    (by simpa only [← hcenter] using hy')
  have hc' := B.all_rectangle_control_to_chart hlarge g k p u h d e (z+tangentOffset a d x)
    (clippingOverlapLower r (tangentOffset a d (signedShortSteps u e)))
    (clippingOverlapUpper r (tangentOffset a d (signedShortSteps u e)))
    (fun j => (hlabels e j).1) (fun j => (hlabels e j).2) n q (coordinateRectangle a L V) hW hinc f hf hc
  have heq := B.tangentSign_step_action_closed hlarge hr k p u h d e (z+tangentOffset a d x)
    (clippingOverlapLower r (tangentOffset a d (signedShortSteps u e)))
    (clippingOverlapUpper r (tangentOffset a d (signedShortSteps u e)))
    (fun j => (hlabels e j).1) (fun j => (hlabels e j).2)
    (fun j => (hb j).1) (fun j => (hb j).2.1) (fun j => (hb j).2.2.1) (fun j => (hb j).2.2.2)
    f hf hc' I s t ht
  exact heq.trans (congrArg (fun z =>
    B.tangentSign (by omega) k p u h d z true (universalMap (subtypeAlternatingHom I.val) s)*t*
      (B.tangentSign (by omega) k p u h d z true (universalMap (subtypeAlternatingHom I.val) s))⁻¹)
    hcenter.symm)

theorem tangent_interval_action (hlarge : 20 ≤ m+1)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2)
    (g : ∀ n, B.CoordinateWindowLaw n)
    (k : ℕ) (p : Fin 2 → ℤ) (u : CutRing) (h : B.TangentChartLaws k p u)
    (d : Fin 2)
    (hsteps : ∀ e j, |ordinary (pointCoordinate (tangentOffset a d (signedShortSteps u e)) j)| ≤ 2*ordinary r)
    (hlabels : ∀ e j,
      (p j ≤ endpointLabel (clippingOverlapLower r (tangentOffset a d (signedShortSteps u e)) j) ∧
       endpointLabel (clippingOverlapLower r (tangentOffset a d (signedShortSteps u e)) j) < p j+k) ∧
      (p j ≤ endpointLabel (clippingOverlapUpper r (tangentOffset a d (signedShortSteps u e)) j) ∧
       endpointLabel (clippingOverlapUpper r (tangentOffset a d (signedShortSteps u e)) j) < p j+k))
    (z : CutRing × CutRing) (L V : Fin 2 → CutRing)
    (hLV : ∀ j, ordinary (L j) ≤ ordinary (V j))
    (A C : ℝ) (x y : CutRing) (hpath : TangentIntervalReach u A C x y)
    (hcenters : ∀ t : CutRing, A ≤ ordinary t → ordinary t ≤ C → ∀ j,
      -ordinary r ≤ ordinary (L j)-ordinary (pointCoordinate (z+tangentOffset a d t) j) ∧
      ordinary (V j)-ordinary (pointCoordinate (z+tangentOffset a d t) j) ≤ ordinary r)
    (n : ℕ) (q : Fin 2 → ℤ)
    (hW : ResolvedBy (fun i => (primitiveTests (a := a) (r := r)
      (coordinateWindowPrimitives n q) i).val) (coordinateRectangle a L V).val)
    (f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm))
    (hf : B.AlignedSmallSupported f)
    (hc : SmallControlled B.c f (B.windowSector (by omega) n (g n) q (coordinateRectangle a L V)))
    (I : ControlAlphabet (Fin (m+1))) (s : UniversalExtension (alternatingGroup I.val))
    (t : BoundedRelationCover M (alternatingGenerator a r m hm)) (ht : t ∈ f.range) :
    B.tangentSign (by omega) k p u h d (z+tangentOffset a d x) true
        (universalMap (subtypeAlternatingHom I.val) s)*t*
      (B.tangentSign (by omega) k p u h d (z+tangentOffset a d x) true
        (universalMap (subtypeAlternatingHom I.val) s))⁻¹ =
    B.tangentSign (by omega) k p u h d (z+tangentOffset a d y) true
        (universalMap (subtypeAlternatingHom I.val) s)*t*
      (B.tangentSign (by omega) k p u h d (z+tangentOffset a d y) true
        (universalMap (subtypeAlternatingHom I.val) s))⁻¹ := by
  induction hpath with
  | refl => rfl
  | @tail y y' _ hstep ih =>
    exact ih.trans (B.tangent_interval_edge_action hlarge hr g k p u h d hsteps hlabels z L V hLV
      A C y y' hstep hcenters n q hW f hf hc I s t ht)

theorem tangent_line_slide (hlarge : 20 ≤ m+1)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2)
    (g : ∀ n, B.CoordinateWindowLaw n)
    (k : ℕ) (p : Fin 2 → ℤ) (u v : CutRing) (huv : u*v=1)
    (h : B.TangentChartLaws k p u)
    (hshort : 4*(1+|ordinary (cutTau^a)|)*(|ordinary u|+|ordinary (cutTau*u)|) ≤ ordinary r)
    (hlabels : ∀ d e j,
      (p j ≤ endpointLabel (clippingOverlapLower r (tangentOffset a d (signedShortSteps u e)) j) ∧
       endpointLabel (clippingOverlapLower r (tangentOffset a d (signedShortSteps u e)) j) < p j+k) ∧
      (p j ≤ endpointLabel (clippingOverlapUpper r (tangentOffset a d (signedShortSteps u e)) j) ∧
       endpointLabel (clippingOverlapUpper r (tangentOffset a d (signedShortSteps u e)) j) < p j+k))
    (d : Fin 2) (z : CutRing × CutRing) (w : CutRing) (L V : Fin 2 → CutRing)
    (hLV : ∀ j, ordinary (L j) ≤ ordinary (V j))
    (hz : ∀ j, -ordinary r ≤ ordinary (L j)-ordinary (pointCoordinate z j) ∧
      ordinary (V j)-ordinary (pointCoordinate z j) ≤ ordinary r)
    (hzw : ∀ j, -ordinary r ≤ ordinary (L j)-ordinary (pointCoordinate (z+tangentOffset a d w) j) ∧
      ordinary (V j)-ordinary (pointCoordinate (z+tangentOffset a d w) j) ≤ ordinary r)
    (c : ℝ)
    (hnear : ∀ j,
      |ordinary (L j)-(ordinary (pointCoordinate z j)+tangentCoefficient a d j*c)| ≤ ordinary r/4 ∧
      |ordinary (V j)-(ordinary (pointCoordinate z j)+tangentCoefficient a d j*c)| ≤ ordinary r/4)
    (n : ℕ) (q : Fin 2 → ℤ)
    (hW : ResolvedBy (fun i => (primitiveTests (a := a) (r := r)
      (coordinateWindowPrimitives n q) i).val) (coordinateRectangle a L V).val)
    (f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm))
    (hf : B.AlignedSmallSupported f)
    (hc : SmallControlled B.c f (B.windowSector (by omega) n (g n) q (coordinateRectangle a L V)))
    (I : ControlAlphabet (Fin (m+1))) (s : UniversalExtension (alternatingGroup I.val))
    (t : BoundedRelationCover M (alternatingGenerator a r m hm)) (ht : t ∈ f.range) :
    B.tangentSign (by omega) k p u h d z true (universalMap (subtypeAlternatingHom I.val) s)*t*
      (B.tangentSign (by omega) k p u h d z true (universalMap (subtypeAlternatingHom I.val) s))⁻¹ =
    B.tangentSign (by omega) k p u h d (z+tangentOffset a d w) true
        (universalMap (subtypeAlternatingHom I.val) s)*t*
      (B.tangentSign (by omega) k p u h d (z+tangentOffset a d w) true
        (universalMap (subtypeAlternatingHom I.val) s))⁻¹ := by
  have hz' := (tangentAllowed_iff a r d z L V (ordinary (0:CutRing))).mpr
    (by simpa only [map_zero,mul_zero,add_zero] using hz)
  have hw' := (tangentAllowed_iff a r d z L V (ordinary w)).mpr
    (by simpa only [pointCoordinate_add,map_add,tangentOffset_coordinate] using hzw)
  have hpath := tangentInterval_connected u v huv _ _
    (tangentAllowed_wide a r u hr.1 d z L V c hshort hnear) 0 w hz' hw'
  have hsteps (e : Fin 5) (j : Fin 2) :
      |ordinary (pointCoordinate (tangentOffset a d (signedShortSteps u e)) j)| ≤ 2*ordinary r := by
    have hh := (tangentOffset_ordinary_bound a d (signedShortSteps u e) j).trans
      (mul_le_mul_of_nonneg_left (signedShortSteps_bound u e) (by positivity : 0 ≤ 1+|ordinary (cutTau^a)|))
    nlinarith [hr.1]
  have heq := B.tangent_interval_action hlarge hr g k p u h d hsteps (hlabels d) z L V hLV
    (tangentAllowedLower a r d z V) (tangentAllowedUpper a r d z L) 0 w hpath
    (fun t h1 h2 j => by
      have hh := (tangentAllowed_iff a r d z L V (ordinary t)).mp ⟨h1,h2⟩ j
      simpa only [pointCoordinate_add,map_add,tangentOffset_coordinate] using hh)
    n q hW f hf hc I s t ht
  simpa only [tangentOffset_zero,add_zero] using heq

end InitialCoverSystem
end ClippedLineSlideAction

end SimpleAmenable
end
end

end OAI
