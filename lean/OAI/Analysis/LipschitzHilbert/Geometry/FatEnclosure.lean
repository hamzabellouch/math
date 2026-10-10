import OAI.Analysis.LipschitzHilbert.Estimates.ClippedSlopeBox
import OAI.Analysis.LipschitzHilbert.Geometry.VerticalRectangle
import OAI.Analysis.LipschitzHilbert.Geometry.RectangleIndicator

namespace OAI

/-! Fat clipped tops have vertical enclosing rectangles. Lacey--Li for
the constant vertical field handles them without a length restriction. -/

noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal
namespace LipschitzHilbert.SlopeBox

def fatEnclosure (T : SlopeBox) (D l r : ℝ)
    (ha : 0 < T.clipLength D l r) (hfat : T.clipLength D l r ≤ 2*D*T.width) : Rectangle :=
  verticalRectangle (T.clipCenter D l r) T.slope (T.clipLength D l r) (2*D*T.width) ha hfat

theorem mem_fatEnclosure (T : SlopeBox) (D l r : ℝ)
    (ha : 0 < T.clipLength D l r) (hfat : T.clipLength D l r ≤ 2*D*T.width)
    (z : ℝ × ℝ) (hx : z.1 ∈ Icc l r) (hz : z ∈ T.radialDilation D) :
    planeCoordinates z ∈ (T.fatEnclosure D l r ha hfat).carrier := by
  obtain ⟨h1,h2⟩ := T.clipped_coordinates D l r z hx hz
  apply mem_verticalRectangle _ _ _ _ _ _ _ h1
  simpa only [show 2*D*T.width/2 = D*T.width by ring] using h2

theorem fatEnclosure_volume_le (T : SlopeBox) (D l r : ℝ) (hD : 0 < D)
    (ha : 0 < T.clipLength D l r) (hfat : T.clipLength D l r ≤ 2*D*T.width)
    (hs : |T.slope| ≤ 1) :
    volume (T.fatEnclosure D l r ha hfat).carrier ≤
      ENNReal.ofReal (8*D^2*T.length*T.width) := by
  apply (volume_verticalRectangle_le _ _ _ _ _ _ hs).trans
  apply ENNReal.ofReal_le_ofReal
  have h := mul_le_mul_of_nonneg_right (T.clipLength_le_dilation D l r)
    (show 0 ≤ 4*D*T.width by have := T.width_pos; positivity)
  nlinarith

theorem fatEnclosure_admissible (T : SlopeBox) (D l r : ℝ)
    (ha : 0 < T.clipLength D l r) (hfat : T.clipLength D l r ≤ 2*D*T.width) :
    (T.fatEnclosure D l r ha hfat).Admissible (fun _ => verticalAxes 0) 0 (1/2) :=
  verticalRectangle_admissible _ _ _ _ _ _

theorem fatEnclosure_average (T : SlopeBox) (D l r : ℝ) (hD : 0 < D)
    (ha : 0 < T.clipLength D l r) (hfat : T.clipLength D l r ≤ 2*D*T.width)
    (hs : |T.slope| ≤ 1) (Q : Set (ℝ × ℝ)) (hQ : MeasurableSet Q)
    (hstrip : ∀ z ∈ Q, z.1 ∈ Icc l r) :
    (volume.prod volume) (Q ∩ T.radialDilation D) /
        ENNReal.ofReal (8*D^2*T.length*T.width) ≤
      (T.fatEnclosure D l r ha hfat).average
        ((planeCoordinates '' Q).indicator (fun _ => (1:ℝ))) := by
  rw [← planeCoordinates_image_measure (Q ∩ T.radialDilation D)]
  apply Rectangle.average_indicator_ge_measure_div
  · exact planeCoordinates.measurableSet_image.mpr hQ
  · rintro _ ⟨z,⟨hzQ,hzD⟩,rfl⟩
    exact ⟨mem_image_of_mem _ hzQ,T.mem_fatEnclosure D l r ha hfat z (hstrip z hzQ) hzD⟩
  · exact T.fatEnclosure_volume_le D l r hD ha hfat hs

end LipschitzHilbert.SlopeBox

end

end OAI
