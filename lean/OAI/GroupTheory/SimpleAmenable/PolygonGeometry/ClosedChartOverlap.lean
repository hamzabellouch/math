import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.RectangularBound

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section ClosedChartOverlap

theorem planar_lift_avoidsCuts {a : ℕ} (p : GenericSquare a) (t : ℝ × ℝ)
    (ht : p.val = (Int.fract t.1,Int.fract t.2)) : AvoidsCuts a t := by
  have h := avoidsCuts_translate p.property.2.2
    ((⌊t.1⌋ : CutRing),(⌊t.2⌋ : CutRing))
  have he : p.val+(ordinary (⌊t.1⌋ : CutRing),ordinary (⌊t.2⌋ : CutRing)) = t := by
    rw [ht]
    apply Prod.ext
    · change Int.fract t.1+ordinary (⌊t.1⌋ : CutRing) = t.1
      rw [map_intCast]
      exact sub_add_cancel _ _
    · change Int.fract t.2+ordinary (⌊t.2⌋ : CutRing) = t.2
      rw [map_intCast]
      exact sub_add_cancel _ _
  rwa [he] at h

theorem coordinateRectangle_strict_lift {a : ℕ} (l h : Fin 2 → CutRing)
    (hlh : ∀ j, ordinary (l j) ≤ ordinary (h j))
    (hlen : ∀ j, ordinary (h j)-ordinary (l j) < 1)
    (p : GenericSquare a) (hp : p ∈ (coordinateRectangle a l h).val) :
    ∃ t : ℝ × ℝ, p.val = (Int.fract t.1,Int.fract t.2) ∧
      (ordinary (l 0) < t.1 ∧ t.1 < ordinary (h 0)) ∧
      (ordinary (l 1) < t.2 ∧ t.2 < ordinary (h 1)) := by
  obtain ⟨t,ht,hx,hy⟩ := coordinateRectangle_lift l h hlh hlen p hp
  have hx' := planar_lift_avoidsCuts p t ht 0 (l 0)
  have hy' := planar_lift_avoidsCuts p t ht 1 (l 1)
  simp only [cutForm,Matrix.cons_val_zero,Matrix.cons_val_one] at hx' hy'
  exact ⟨t,ht,⟨lt_of_le_of_ne hx.1 (Ne.symm hx'),hx.2⟩,
    ⟨lt_of_le_of_ne hy.1 (Ne.symm hy'),hy.2⟩⟩

theorem clippedSlope_agree_on_closed_rectangle {a : ℕ} (r : CutRing) (j : Fin 4)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2)
    (u v : CutRing × CutRing) (l h : Fin 2 → CutRing)
    (hlh : ∀ k, ordinary (l k) ≤ ordinary (h k))
    (hlen : ∀ k, ordinary (h k)-ordinary (l k) < 1)
    (hu : ∀ k, -ordinary r ≤ ordinary (l k)-ordinary (pointCoordinate u k) ∧
      ordinary (h k)-ordinary (pointCoordinate u k) ≤ ordinary r)
    (hv : ∀ k, -ordinary r ≤ ordinary (l k)-ordinary (pointCoordinate v k) ∧
      ordinary (h k)-ordinary (pointCoordinate v k) ≤ ordinary r)
    (hline : integralCutForm a j u = integralCutForm a j v) :
    spatialTranslate u (clippedSlopePrimitive a r j) ⊓ coordinateRectangle a l h =
      spatialTranslate v (clippedSlopePrimitive a r j) ⊓ coordinateRectangle a l h := by
  apply Subtype.ext
  ext p
  change (p ∈ (spatialTranslate u (clippedSlopePrimitive a r j)).val ∧
    p ∈ (coordinateRectangle a l h).val) ↔
    (p ∈ (spatialTranslate v (clippedSlopePrimitive a r j)).val ∧
    p ∈ (coordinateRectangle a l h).val)
  by_cases hp : p ∈ (coordinateRectangle a l h).val
  · obtain ⟨t,ht,hx,hy⟩ := coordinateRectangle_strict_lift l h hlh hlen p hp
    have hbox (w : CutRing × CutRing)
        (hw : ∀ k : Fin 2, -ordinary r ≤ ordinary (l k)-ordinary (pointCoordinate w k) ∧
          ordinary (h k)-ordinary (pointCoordinate w k) ≤ ordinary r) :
        (-ordinary r < t.1-ordinary w.1 ∧ t.1-ordinary w.1 < ordinary r) ∧
          (-ordinary r < t.2-ordinary w.2 ∧ t.2-ordinary w.2 < ordinary r) := by
      have hw0 := hw 0
      have hw1 := hw 1
      simp only [pointCoordinate,ite_true,Fin.isValue,show (1:Fin 2) ≠ 0 by decide,ite_false] at hw0 hw1
      constructor <;> constructor <;> linarith
    rw [translated_clippedSlope_lift r j hr u p t ht (hbox u hu),
      translated_clippedSlope_lift r j hr v p t ht (hbox v hv),hline]
  · simp only [hp,and_false]

end ClosedChartOverlap

section FullTangentOverlap

noncomputable def orderedCutMax (x y : CutRing) : CutRing :=
  if ordinary x ≤ ordinary y then y else x
noncomputable def orderedCutMin (x y : CutRing) : CutRing :=
  if ordinary x ≤ ordinary y then x else y

@[simp] theorem ordinary_orderedCutMax (x y : CutRing) :
    ordinary (orderedCutMax x y) = max (ordinary x) (ordinary y) := by
  unfold orderedCutMax
  split_ifs with h
  · exact (max_eq_right h).symm
  · exact (max_eq_left (le_of_not_ge h)).symm

@[simp] theorem ordinary_orderedCutMin (x y : CutRing) :
    ordinary (orderedCutMin x y) = min (ordinary x) (ordinary y) := by
  unfold orderedCutMin
  split_ifs with h
  · exact (min_eq_left h).symm
  · exact (min_eq_right (le_of_not_ge h)).symm

noncomputable def clippingOverlapLower (r : CutRing) (t : CutRing × CutRing) (j : Fin 2) : CutRing :=
  orderedCutMax (-r) (pointCoordinate t j-r)
noncomputable def clippingOverlapUpper (r : CutRing) (t : CutRing × CutRing) (j : Fin 2) : CutRing :=
  orderedCutMin r (pointCoordinate t j+r)

theorem clippingOverlap_bounds (r : CutRing) (t : CutRing × CutRing)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2)
    (ht : ∀ j, |ordinary (pointCoordinate t j)| ≤ 2*ordinary r) (j : Fin 2) :
    ordinary (clippingOverlapLower r t j) ≤ ordinary (clippingOverlapUpper r t j) ∧
    ordinary (clippingOverlapUpper r t j)-ordinary (clippingOverlapLower r t j) < 1 ∧
    (-ordinary r ≤ ordinary (clippingOverlapLower r t j) ∧
      ordinary (clippingOverlapUpper r t j) ≤ ordinary r) ∧
    (-ordinary r ≤ ordinary (clippingOverlapLower r t j)-ordinary (pointCoordinate t j) ∧
      ordinary (clippingOverlapUpper r t j)-ordinary (pointCoordinate t j) ≤ ordinary r) := by
  have hh := abs_le.mp (ht j)
  simp only [clippingOverlapLower,clippingOverlapUpper,ordinary_orderedCutMax,
    ordinary_orderedCutMin,map_sub,map_neg,map_add]
  have h1 := le_max_left (-ordinary r) (ordinary (pointCoordinate t j)-ordinary r)
  have h2 := le_max_right (-ordinary r) (ordinary (pointCoordinate t j)-ordinary r)
  have h3 := min_le_left (ordinary r) (ordinary (pointCoordinate t j)+ordinary r)
  have h4 := min_le_right (ordinary r) (ordinary (pointCoordinate t j)+ordinary r)
  refine ⟨max_le (le_min (by linarith [hr.1]) (by linarith))
    (le_min (by linarith) (by linarith [hr.1])),by linarith [hr.2],⟨h1,h3⟩,?_,?_⟩ <;> linarith

theorem exists_full_overlap_window (a : ℕ) (r u : CutRing) :
    ∃ k : ℕ, ∃ p : Fin 2 → ℤ, ∀ d : Fin 2, ∀ e : Fin 5, ∀ j : Fin 2,
      (p j ≤ endpointLabel (clippingOverlapLower r (tangentOffset a d (signedShortSteps u e)) j) ∧
       endpointLabel (clippingOverlapLower r (tangentOffset a d (signedShortSteps u e)) j) < p j+k) ∧
      (p j ≤ endpointLabel (clippingOverlapUpper r (tangentOffset a d (signedShortSteps u e)) j) ∧
       endpointLabel (clippingOverlapUpper r (tangentOffset a d (signedShortSteps u e)) j) < p j+k) := by
  let q (i : Fin 2 × Fin 5 × Bool) (j : Fin 2) : ℤ :=
    endpointLabel (if i.2.2 then clippingOverlapUpper r (tangentOffset a i.1 (signedShortSteps u i.2.1)) j
      else clippingOverlapLower r (tangentOffset a i.1 (signedShortSteps u i.2.1)) j)
  obtain ⟨k,p,hp⟩ := finite_coordinate_windows_container (fun _ : Fin 2 × Fin 5 × Bool => 1) q
  refine ⟨k,p,fun d e j => ?_⟩
  have hL := hp (d,e,false) j
  have hU := hp (d,e,true) j
  dsimp [q] at hL hU
  omega

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem tangentSign_step_action_closed (hlarge : 20 ≤ m+1)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2)
    (k : ℕ) (p : Fin 2 → ℤ) (u : CutRing) (h : B.TangentChartLaws k p u)
    (d : Fin 2) (e : Fin 5) (z : CutRing × CutRing)
    (l v : Fin 2 → CutRing)
    (hl : ∀ j, p j ≤ endpointLabel (l j) ∧ endpointLabel (l j) < p j+k)
    (hv : ∀ j, p j ≤ endpointLabel (v j) ∧ endpointLabel (v j) < p j+k)
    (hlv : ∀ j, ordinary (l j) ≤ ordinary (v j))
    (hlen : ∀ j, ordinary (v j)-ordinary (l j) < 1)
    (hbox : ∀ j, -ordinary r ≤ ordinary (l j) ∧ ordinary (v j) ≤ ordinary r)
    (hbox' : ∀ j, -ordinary r ≤ ordinary (l j)-ordinary
          (pointCoordinate (tangentOffset a d (signedShortSteps u e)) j) ∧
        ordinary (v j)-ordinary
          (pointCoordinate (tangentOffset a d (signedShortSteps u e)) j) ≤ ordinary r)
    (f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm))
    (hf : B.AlignedSmallSupported f)
    (hc : SmallControlled B.c f (B.fullGeometricSector (by omega)
      (translatedTemplate (tangentChartTemplate a k p d (signedShortSteps u e)) z)
        (h d e z) (spatialTranslate z (coordinateRectangle a l v))))
    (I : ControlAlphabet (Fin (m+1))) (s : UniversalExtension (alternatingGroup I.val)) :
    ∀ x ∈ f.range,
      B.tangentSign (by omega) k p u h d z true (universalMap (subtypeAlternatingHom I.val) s)*x*
        (B.tangentSign (by omega) k p u h d z true (universalMap (subtypeAlternatingHom I.val) s))⁻¹ =
      B.tangentSign (by omega) k p u h d (z+tangentOffset a d (signedShortSteps u e)) true
          (universalMap (subtypeAlternatingHom I.val) s)*x*
        (B.tangentSign (by omega) k p u h d (z+tangentOffset a d (signedShortSteps u e)) true
          (universalMap (subtypeAlternatingHom I.val) s))⁻¹ := by
  rw [B.tangentSign_first (by omega) k p u h d z e true,
    B.tangentSign_second (by omega) k p u h d z e true]
  apply B.chart_action_transfer hlarge _ (h d e z) _ _ _
    (tangentChart_first_resolved p d _ z) (tangentChart_second_resolved p d _ z)
    (tangentChart_rectangle_resolved p d _ z l v hl hv) _ f hf hc I s
  have he := clippedSlope_agree_on_closed_rectangle (a := a) r (slopeDirection d) hr
    (0 : CutRing × CutRing) (tangentOffset a d (signedShortSteps u e)) l v hlv hlen
    (by simpa [pointCoordinate] using hbox) hbox'
    (by simp only [integralCutForm_zero,integralCutForm_tangentOffset])
  have he' := congrArg (spatialTranslate z) he
  simpa only [spatialTranslate_inter,← spatialTranslate_add,add_zero] using he'

end InitialCoverSystem
end FullTangentOverlap

end SimpleAmenable
end
end

end OAI
