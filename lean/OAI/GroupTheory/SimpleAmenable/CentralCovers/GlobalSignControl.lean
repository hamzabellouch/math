import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.UniformTangentTransport
import OAI.GroupTheory.SimpleAmenable.Homology.GlobalTangentChain
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.TangentChartTemplates

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section GlobalSignControl
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem tangentSign_eq (hlarge : 15 < m+1)
    (k k' : ℕ) (p p' : Fin 2 → ℤ) (u u' : CutRing)
    (h : B.TangentChartLaws k p u) (h' : B.TangentChartLaws k' p' u')
    (d : Fin 2) (z : CutRing × CutRing) (positive : Bool) :
    B.tangentSign hlarge k p u h d z positive = B.tangentSign hlarge k' p' u' h' d z positive := by
  unfold tangentSign
  refine B.fullGeometricSector_shared_primitive hlarge _ _
    (Sum.inl (0 : Fin 2)) (Sum.inl (0 : Fin 2)) ?_ (h d 0 z) (h' d 0 z) _ ?_
  · simp only [translatedTemplate,tangentChartTemplate,ite_true]
  · intro x y he
    have hh := he ()
    change x ∈ (spatialTranslate (z+0) (initialTest a r (slopeTestIndex d))).val ↔
      y ∈ (spatialTranslate (z+0) (initialTest a r (slopeTestIndex d))).val at hh
    simp only [add_zero,initialTest_slope] at hh
    cases positive with
    | false => simpa using not_congr hh
    | true => simpa using hh

theorem all_rectangle_control_to_sign (hlarge : 20 ≤ m+1)
    (g : ∀ n, B.CoordinateWindowLaw n)
    (k : ℕ) (p : Fin 2 → ℤ) (u : CutRing) (h : B.TangentChartLaws k p u)
    (d : Fin 2) (z : CutRing × CutRing) (positive : Bool) (l v : Fin 2 → CutRing)
    (hl : ∀ j, p j ≤ endpointLabel (l j) ∧ endpointLabel (l j) < p j+k)
    (hv : ∀ j, p j ≤ endpointLabel (v j) ∧ endpointLabel (v j) < p j+k)
    (hside : coordinateRectangle a l v ≤ if positive then clippedSlopePrimitive a r (slopeDirection d)
      else (clippedSlopePrimitive a r (slopeDirection d))ᶜ)
    (n : ℕ) (q : Fin 2 → ℤ) (W : polygonAlgebra a)
    (hW : ResolvedBy (fun i => (primitiveTests (a := a) (r := r)
      (coordinateWindowPrimitives n q) i).val) W.val)
    (hinc : W ≤ spatialTranslate z (coordinateRectangle a l v))
    (f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm))
    (hf : B.AlignedSmallSupported f)
    (hc : SmallControlled B.c f (B.windowSector (by omega) n (g n) q W)) :
    SmallControlled B.c f (B.tangentSign (by omega) k p u h d z positive) := by
  apply B.control_trans hlarge f _ _ hf (B.tangentSign_supported (by omega) k p u h d z positive)
    (B.all_rectangle_control_to_chart hlarge g k p u h d 0 z l v hl hv n q W hW hinc f hf hc)
  unfold tangentSign
  apply B.fullGeometricSector_small_control
  cases positive with
  | false => exact spatialTranslate_mono z hside
  | true => exact spatialTranslate_mono z hside

theorem tangentSign_constant_action (hlarge : 20 ≤ m+1)
    (k : ℕ) (p : Fin 2 → ℤ) (u : CutRing) (h : B.TangentChartLaws k p u)
    (d : Fin 2) (z : CutRing × CutRing) (positive : Bool)
    (f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm))
    (hf : B.AlignedSmallSupported f)
    (hc : SmallControlled B.c f (B.tangentSign (by omega) k p u h d z positive))
    (I : ControlAlphabet (Fin (m+1))) (s : UniversalExtension (alternatingGroup I.val))
    (x : BoundedRelationCover M (alternatingGenerator a r m hm)) (hx : x ∈ f.range) :
    B.tangentSign (by omega) k p u h d z true (universalMap (subtypeAlternatingHom I.val) s)*x*
      (B.tangentSign (by omega) k p u h d z true (universalMap (subtypeAlternatingHom I.val) s))⁻¹ =
    (if positive then B.c (subtypeAlternatingHom I.val (universalProjection (alternatingGroup I.val) s)) else 1)*x*
      (if positive then B.c (subtypeAlternatingHom I.val (universalProjection (alternatingGroup I.val) s)) else 1)⁻¹ := by
  cases positive with
  | true =>
    have hh := hc I s x hx
    have he := DFunLike.congr_fun (universalMap_spec (subtypeAlternatingHom I.val)) s
    simp only [MonoidHom.comp_apply] at he
    simpa only [MonoidHom.comp_apply,he,ite_true] using hh
  | false =>
    have hh := small_control_transfer _ B.c B.constant_aligned B.disjoint_aligned f _ hf hc I.val
      (B.tangentSign (by omega) k p u h d z true (universalMap (subtypeAlternatingHom I.val) s))
      (B.tangentSign_supported (by omega) k p u h d z true I ⟨s,rfl⟩)
      (by have hI := I.property.2; simp only [Fintype.card_fin]; omega)
      (fun J t => B.tangentSign_opposite_commute (by omega) k p u h d z _ _) x hx
    simp only [Bool.false_eq_true,ite_false,inv_one,one_mul,mul_one]
    rw [hh.eq,mul_assoc,mul_inv_cancel,mul_one]

end InitialCoverSystem
end GlobalSignControl

end SimpleAmenable
end
end

end OAI
