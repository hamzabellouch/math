import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.LabelShiftedCharts
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.RectangularBound

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section GlobalTangentChain

theorem translated_rectangle_window {a k : ℕ} {r : CutRing}
    (p : Fin 2 → ℤ) (z : CutRing × CutRing) (l v : Fin 2 → CutRing)
    (hl : ∀ j, p j ≤ endpointLabel (l j) ∧ endpointLabel (l j) < p j+k)
    (hv : ∀ j, p j ≤ endpointLabel (v j) ∧ endpointLabel (v j) < p j+k) :
    ResolvedBy (fun i => (InitialCoverSystem.primitiveTests (a := a) (r := r)
      (coordinateWindowPrimitives k (fun j => pointLabel z j+p j)) i).val)
      (spatialTranslate z (coordinateRectangle a l v)).val := by
  rw [spatialTranslate_coordinateRectangle]
  have hL j : pointLabel z j+p j ≤ endpointLabel (l j+pointCoordinate z j) ∧
      endpointLabel (l j+pointCoordinate z j) < pointLabel z j+p j+k := by
    simp only [endpointLabel_add,pointLabel]
    have hh := hl j
    omega
  have hV j : pointLabel z j+p j ≤ endpointLabel (v j+pointCoordinate z j) ∧
      endpointLabel (v j+pointCoordinate z j) < pointLabel z j+p j+k := by
    simp only [endpointLabel_add,pointLabel]
    have hh := hv j
    omega
  intro x y he
  exact and_congr
    (coordinateInterval_window k _ 0 _ _ (hL 0) (hV 0) x y he)
    (coordinateInterval_window k _ 1 _ _ (hL 1) (hV 1) x y he)

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem all_rectangle_control_to_chart (hlarge : 20 ≤ m+1)
    (g : ∀ n, B.CoordinateWindowLaw n)
    (k : ℕ) (p : Fin 2 → ℤ) (u : CutRing) (h : B.TangentChartLaws k p u)
    (d : Fin 2) (e : Fin 5) (z : CutRing × CutRing) (l v : Fin 2 → CutRing)
    (hl : ∀ j, p j ≤ endpointLabel (l j) ∧ endpointLabel (l j) < p j+k)
    (hv : ∀ j, p j ≤ endpointLabel (v j) ∧ endpointLabel (v j) < p j+k)
    (n : ℕ) (q : Fin 2 → ℤ) (W : polygonAlgebra a)
    (hW : ResolvedBy (fun i => (primitiveTests (a := a) (r := r)
      (coordinateWindowPrimitives n q) i).val) W.val)
    (hinc : W ≤ spatialTranslate z (coordinateRectangle a l v))
    (f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm))
    (hf : B.AlignedSmallSupported f)
    (hc : SmallControlled B.c f (B.windowSector (by omega) n (g n) q W)) :
    SmallControlled B.c f (B.fullGeometricSector (by omega)
      (translatedTemplate (tangentChartTemplate a k p d (signedShortSteps u e)) z)
        (h d e z) (spatialTranslate z (coordinateRectangle a l v))) := by
  apply B.control_trans hlarge f _ _ hf
    (B.fullGeometricSector_supported (by omega) _ _ _
      (tangentChart_rectangle_resolved p d _ z l v hl hv)) hc
  rw [B.tangentChartSector_eq_window (by omega) k p u h k le_rfl (g k) d e z l v hl hv]
  exact B.all_window_control (by omega) g n k q (fun j => pointLabel z j+p j)
    W _ hinc hW (translated_rectangle_window p z l v hl hv)

theorem tangent_chain_unbounded (hlarge : 20 ≤ m+1)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2)
    (g : ∀ n, B.CoordinateWindowLaw n)
    (k : ℕ) (p : Fin 2 → ℤ) (u : CutRing) (h : B.TangentChartLaws k p u)
    (l v : Fin 2 → CutRing)
    (hl : ∀ j, p j ≤ endpointLabel (l j) ∧ endpointLabel (l j) < p j+k)
    (hv : ∀ j, p j ≤ endpointLabel (v j) ∧ endpointLabel (v j) < p j+k)
    (hlv : ∀ j, ordinary (l j) ≤ ordinary (v j))
    (hlen : ∀ j, ordinary (v j)-ordinary (l j) < 1)
    (hbox : ∀ j, -ordinary r < ordinary (l j) ∧ ordinary (v j) < ordinary r)
    (hbox' : ∀ (d : Fin 2) (e : Fin 5) (j : Fin 2),
      -ordinary r < ordinary (l j)-ordinary (pointCoordinate (tangentOffset a d (signedShortSteps u e)) j) ∧
      ordinary (v j)-ordinary (pointCoordinate (tangentOffset a d (signedShortSteps u e)) j) < ordinary r)
    (n : ℕ) (q : Fin 2 → ℤ) (W : polygonAlgebra a)
    (hW : ResolvedBy (fun i => (primitiveTests (a := a) (r := r)
      (coordinateWindowPrimitives n q) i).val) W.val)
    (d : Fin 2) (T : ℕ) (z : ℕ → CutRing × CutRing) (e : ℕ → Fin 5)
    (hz : ∀ i, i < T → z (i+1) = z i+tangentOffset a d (signedShortSteps u (e i)))
    (hinc : ∀ i, i < T → W ≤ spatialTranslate (z i) (coordinateRectangle a l v))
    (f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm))
    (hf : B.AlignedSmallSupported f)
    (hc : SmallControlled B.c f (B.windowSector (by omega) n (g n) q W))
    (I : ControlAlphabet (Fin (m+1))) (s : UniversalExtension (alternatingGroup I.val))
    (x : BoundedRelationCover M (alternatingGenerator a r m hm)) (hx : x ∈ f.range) :
    B.tangentSign (by omega) k p u h d (z 0) true (universalMap (subtypeAlternatingHom I.val) s)*x*
      (B.tangentSign (by omega) k p u h d (z 0) true (universalMap (subtypeAlternatingHom I.val) s))⁻¹ =
    B.tangentSign (by omega) k p u h d (z T) true (universalMap (subtypeAlternatingHom I.val) s)*x*
      (B.tangentSign (by omega) k p u h d (z T) true (universalMap (subtypeAlternatingHom I.val) s))⁻¹ := by
  have hstep i (hi : i < T) :
      B.tangentSign (by omega) k p u h d (z i) true (universalMap (subtypeAlternatingHom I.val) s)*x*
        (B.tangentSign (by omega) k p u h d (z i) true (universalMap (subtypeAlternatingHom I.val) s))⁻¹ =
      B.tangentSign (by omega) k p u h d (z (i+1)) true (universalMap (subtypeAlternatingHom I.val) s)*x*
        (B.tangentSign (by omega) k p u h d (z (i+1)) true (universalMap (subtypeAlternatingHom I.val) s))⁻¹ := by
    rw [hz i hi]
    exact B.tangentSign_step_action hlarge hr k p u h d (e i) (z i) l v hl hv hlv hlen hbox
      (hbox' d (e i)) f hf
      (B.all_rectangle_control_to_chart hlarge g k p u h d (e i) (z i) l v hl hv n q W hW (hinc i hi) f hf hc)
      I s x hx
  have he t (ht : t ≤ T) :
      B.tangentSign (by omega) k p u h d (z 0) true (universalMap (subtypeAlternatingHom I.val) s)*x*
        (B.tangentSign (by omega) k p u h d (z 0) true (universalMap (subtypeAlternatingHom I.val) s))⁻¹ =
      B.tangentSign (by omega) k p u h d (z t) true (universalMap (subtypeAlternatingHom I.val) s)*x*
        (B.tangentSign (by omega) k p u h d (z t) true (universalMap (subtypeAlternatingHom I.val) s))⁻¹ := by
    induction t with
    | zero => rfl
    | succ t ih => exact (ih (by omega)).trans (hstep t (by omega))
  exact he T le_rfl

end InitialCoverSystem
end GlobalTangentChain

end SimpleAmenable
end
end

end OAI
