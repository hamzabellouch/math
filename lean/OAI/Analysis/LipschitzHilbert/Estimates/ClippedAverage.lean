import OAI.Analysis.LipschitzHilbert.Geometry.ClippedEnclosure
import OAI.Analysis.LipschitzHilbert.Geometry.RectangleIndicator

namespace OAI

/-! The indicator average of the actual thin enclosing rectangle controls
intersection with a dilated top. The area cost is explicitly quadratic. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LipschitzHilbert.SlopeBox

theorem thinEnclosure_average (T : SlopeBox) (D l r : ℝ) (hD : 0 < D)
    (ha : 0 < T.clipLength D l r) (hthin : 2*D*T.width ≤ T.clipLength D l r)
    (Q : Set (ℝ × ℝ)) (hQ : MeasurableSet Q) (hstrip : ∀ z ∈ Q, z.1 ∈ Icc l r) :
    (volume.prod volume) (Q ∩ T.radialDilation D) /
        ENNReal.ofReal (8*D^2*T.length*T.width) ≤
      (T.thinEnclosure D l r hD ha hthin).average
        ((planeCoordinates '' Q).indicator (fun _ => (1:ℝ))) := by
  rw [← planeCoordinates_image_measure (Q ∩ T.radialDilation D)]
  apply Rectangle.average_indicator_ge_measure_div
  · exact planeCoordinates.measurableSet_image.mpr hQ
  · rintro _ ⟨z,⟨hzQ,hzD⟩,rfl⟩
    exact ⟨mem_image_of_mem _ hzQ, T.mem_thinEnclosure D l r hD ha hthin z (hstrip z hzQ) hzD⟩
  · exact T.thinEnclosure_volume_le D l r hD ha hthin

end LipschitzHilbert.SlopeBox

end

end OAI
