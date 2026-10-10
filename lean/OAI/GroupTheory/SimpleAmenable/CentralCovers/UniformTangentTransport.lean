import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.StarAtomLaw
import OAI.GroupTheory.SimpleAmenable.Configurations.SymmetricCharts

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section UniformTangentTransport
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem tangent_transport_uniform (hlarge : 20 ≤ m+1)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2)
    (s u v : CutRing) (hs : 0 < ordinary s) (hsr : ordinary s < ordinary r/2)
    (huv : u*v=1)
    (hshort : (1+|ordinary (cutTau^a)|)*(|ordinary u|+|ordinary (cutTau*u)|) < ordinary s/4)
    (h : B.TangentChartLaws (symmetricWindowLength s) (symmetricWindowStart s) u)
    {A C D E : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (hD : 0 ≤ D) (hE : 0 ≤ E) :
    ∃ N : ℕ, 160 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ g : B.CoordinateWindowLaw n,
      ∀ (t : Fin 2 → ℕ) (ht : ∀ j, t j ≤ n) (p : Fin 2 → ℤ) (L V : Fin 2 → CutRing),
      (∀ j, ordinary (L j) ≤ ordinary (V j)) →
      (∀ j, p j ≤ endpointLabel (L j) ∧ endpointLabel (L j) < p j+t j) →
      (∀ j, p j ≤ endpointLabel (V j) ∧ endpointLabel (V j) < p j+t j) →
      ∀ w : CutRing, |ordinary w| ≤ A/(n:ℝ) → |(endpointLabel w:ℝ)| ≤ C*(n:ℝ) →
      ∀ (d : Fin 2) (z₀ : CutRing × CutRing),
      (∀ j, |(pointLabel z₀ j+symmetricWindowStart s j-p j:ℝ)| ≤ E*(n:ℝ)) →
      (∀ j, |ordinary (L j)-ordinary (pointCoordinate z₀ j)| ≤ D/(n:ℝ)) →
      (∀ j, |ordinary (V j)-ordinary (pointCoordinate z₀ j)| ≤ D/(n:ℝ)) →
      ∀ f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm),
      B.AlignedSmallSupported f →
      (∀ j, SmallControlled B.c f
        (B.axisSector (by omega) n g j (t j) (ht j) (p j) (coordinateInterval a j (L j) (V j)))) →
      SmallControlled B.c f (B.tangentSign (by omega) (symmetricWindowLength s)
        (symmetricWindowStart s) u h d z₀ true) →
      SmallControlled B.c f (B.tangentSign (by omega) (symmetricWindowLength s)
        (symmetricWindowStart s) u h d (z₀+tangentOffset a d w) true) := by
  obtain ⟨K,hK,N₁,hN₁,hgeo⟩ := uniform_tangent_chart_geometry a u v s huv hs hshort hA hC hD hE
  have hl := fun j => (symmetricWindow_labels s j).1
  have hv := fun j => (symmetricWindow_labels s j).2.2
  have hlen : ∀ _ : Fin 2, ordinary s-ordinary (-s) < 1 := by
    intro j
    rw [map_neg]
    linarith [hr.2]
  have hbox (j : Fin 2) : -ordinary r < ordinary (-s) ∧ ordinary s < ordinary r := by
    rw [map_neg]
    constructor <;> linarith [hr.1]
  obtain ⟨N₂,hN₂,hchain⟩ := B.tangent_chart_chain_control hlarge hr hK
    (by linarith : 0 < ordinary s/4) (symmetricWindowLength s) (symmetricWindowStart s) u h
    (fun _ => -s) (fun _ => s) hl hv (fun _ => by rw [map_neg]; linarith) hlen hbox
    (fun d e j => (symmetric_chart_overlap_boxes a r s u hs hsr hshort d e j).2)
  refine ⟨max N₁ N₂,hN₂.trans (le_max_right _ _),?_⟩
  intro n hn g t ht p L V hLV hL hV w hw hw' d z₀ hp hLo hVo f hf hc hstart
  have hn₁ : N₁ ≤ n := (le_max_left _ _).trans hn
  have hn₂ : N₂ ≤ n := (le_max_right _ _).trans hn
  obtain ⟨T,z,e,hz0,hzT,hstep,hpq,hlo,hup⟩ := hgeo n hn₁ w hw hw' d z₀
    (symmetricWindowStart s) p L V hp hLo hVo
  have hh := hchain n hn₂ g t ht p L V hLV hL hV d T z e hstep
    (fun i _ => hpq i) (fun i _ => by simpa only [map_neg] using hlo i)
    (fun i _ => hup i) f hf hc (by simpa only [hz0] using hstart)
  simpa only [hzT] using hh

end InitialCoverSystem
end UniformTangentTransport

section ContainingChartWindow
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem tangentChartSector_eq_containing_window (hlarge : 15 < m+1)
    (k : ℕ) (q : Fin 2 → ℤ) (u : CutRing) (h : B.TangentChartLaws k q u)
    (n : ℕ) (g : B.CoordinateWindowLaw n) (p : Fin 2 → ℤ)
    (d : Fin 2) (e : Fin 5) (z : CutRing × CutRing)
    (hstart : ∀ j, p j ≤ pointLabel z j+q j)
    (hend : ∀ j, pointLabel z j+q j+k ≤ p j+n)
    (l v : Fin 2 → CutRing)
    (hl : ∀ j, q j ≤ endpointLabel (l j) ∧ endpointLabel (l j) < q j+k)
    (hv : ∀ j, q j ≤ endpointLabel (v j) ∧ endpointLabel (v j) < q j+k) :
    B.fullGeometricSector hlarge
      (translatedTemplate (tangentChartTemplate a k q d (signedShortSteps u e)) z) (h d e z)
      (spatialTranslate z (coordinateRectangle a l v)) =
    B.windowSector hlarge n g p (spatialTranslate z (coordinateRectangle a l v)) := by
  apply B.chartCoordinateSector_eq_window hlarge n g p
    _ (h d e z) Sum.inr Prod.fst (fun i => z+(coordinateWindowPrimitives k q i).2)
  · intro i
    rfl
  · intro i
    change p i.1 ≤ pointLabel (z+(coordinateWindowPrimitives k q i).2) i.1
    simp only [pointLabel_add,coordinateWindow_pointLabel]
    have hh := hstart i.1
    omega
  · intro i
    change pointLabel (z+(coordinateWindowPrimitives k q i).2) i.1 < p i.1+(n-1:ℕ)
    simp only [pointLabel_add,coordinateWindow_pointLabel]
    have hi := i.2.isLt
    have hh := hend i.1
    omega
  · intro x y he
    apply (translatedTemplate_resolved (a := a) (r := r) (coordinateWindowPrimitives k q)
      (coordinateRectangle a l v) (fun x y he => and_congr
        (coordinateLabelWindow_resolved k q 0 (l 0) (v 0) (hl 0) (hv 0) x y he)
        (coordinateLabelWindow_resolved k q 1 (l 1) (v 1) (hl 1) (hv 1) x y he)) z) x y
    simpa only [primitiveTests,primitiveFamilyTests,translatedTemplate,coordinateWindowPrimitives,
      initialTest_coordinate] using he

theorem tangentSign_supported (hlarge : 15 < m+1)
    (k : ℕ) (q : Fin 2 → ℤ) (u : CutRing) (h : B.TangentChartLaws k q u)
    (d : Fin 2) (z : CutRing × CutRing) (positive : Bool) :
    B.AlignedSmallSupported (B.tangentSign hlarge k q u h d z positive) := by
  unfold tangentSign
  apply B.fullGeometricSector_supported
  have hh := tangentChart_first_resolved (a := a) (r := r) (k := k) q d (signedShortSteps u 0) z
  cases positive with
  | false => exact fun x y he => not_congr (hh x y he)
  | true => exact hh

theorem tangentSign_control_from_rectangle (hlarge : 20 ≤ m+1)
    (k : ℕ) (q : Fin 2 → ℤ) (u : CutRing) (h : B.TangentChartLaws k q u)
    (n : ℕ) (g : B.CoordinateWindowLaw n) (p : Fin 2 → ℤ)
    (d : Fin 2) (z : CutRing × CutRing) (positive : Bool)
    (hstart : ∀ j, p j ≤ pointLabel z j+q j)
    (hend : ∀ j, pointLabel z j+q j+k ≤ p j+n)
    (l v : Fin 2 → CutRing)
    (hl : ∀ j, q j ≤ endpointLabel (l j) ∧ endpointLabel (l j) < q j+k)
    (hv : ∀ j, q j ≤ endpointLabel (v j) ∧ endpointLabel (v j) < q j+k)
    (hside : coordinateRectangle a l v ≤ if positive then clippedSlopePrimitive a r (slopeDirection d)
      else (clippedSlopePrimitive a r (slopeDirection d))ᶜ)
    (R : polygonAlgebra a) (hR : R ≤ spatialTranslate z (coordinateRectangle a l v))
    (f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm))
    (hf : B.AlignedSmallSupported f)
    (hc : SmallControlled B.c f (B.windowSector (by omega) n g p R)) :
    SmallControlled B.c f (B.tangentSign (by omega) k q u h d z positive) := by
  let P := translatedTemplate (tangentChartTemplate a k q d (signedShortSteps u 0)) z
  let V := spatialTranslate z (coordinateRectangle a l v)
  have hV : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) P i).val) V.val :=
    tangentChart_rectangle_resolved q d _ z l v hl hv
  have he := B.tangentChartSector_eq_containing_window (by omega) k q u h n g p d 0 z hstart hend l v hl hv
  have hcV : SmallControlled B.c f (B.fullGeometricSector (by omega) P (h d 0 z) V) := by
    rw [he]
    refine B.control_trans hlarge f (B.windowSector (by omega) n g p R) _ hf ?_ hc ?_
    · rw [← he]
      exact B.fullGeometricSector_supported (by omega) P (h d 0 z) V hV
    · exact B.fullGeometricSector_small_control (by omega) _ _ R V hR
  apply B.control_trans hlarge f _ _ hf (B.tangentSign_supported (by omega) k q u h d z positive) hcV
  unfold tangentSign
  apply B.fullGeometricSector_small_control
  cases positive with
  | false => exact spatialTranslate_mono z hside
  | true => exact spatialTranslate_mono z hside

end InitialCoverSystem
end ContainingChartWindow

end SimpleAmenable
end
end

end OAI
