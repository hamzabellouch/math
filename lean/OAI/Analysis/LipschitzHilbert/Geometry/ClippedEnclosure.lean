import OAI.Analysis.LipschitzHilbert.Estimates.ClippedSlopeBox
import OAI.Analysis.LipschitzHilbert.Estimates.SlopeAdmissibility

namespace OAI

/-! The thin enclosing rectangle for an actual horizontally clipped top
box. The long side is controlled by the testing strip before the published
length restriction is invoked. -/

noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal
namespace LipschitzHilbert.SlopeBox

def thinEnclosure (T : SlopeBox) (D l r : ℝ) (hD : 0 < D)
    (ha : 0 < T.clipLength D l r) (hthin : 2*D*T.width ≤ T.clipLength D l r) : Rectangle :=
  slopeRectangle (T.clipCenter D l r) T.slope (T.clipLength D l r) (2*D*T.width)
    ha (by have := T.width_pos; positivity) hthin

theorem mem_thinEnclosure (T : SlopeBox) (D l r : ℝ) (hD : 0 < D)
    (ha : 0 < T.clipLength D l r) (hthin : 2*D*T.width ≤ T.clipLength D l r)
    (z : ℝ × ℝ) (hx : z.1 ∈ Icc l r) (hz : z ∈ T.radialDilation D) :
    planeCoordinates z ∈ (T.thinEnclosure D l r hD ha hthin).carrier := by
  obtain ⟨h1,h2⟩ := T.clipped_coordinates D l r z hx hz
  apply mem_slopeRectangle _ _ _ _ _ _ _ _ h1
  simpa only [show 2*D*T.width/2 = D*T.width by ring] using h2

theorem thinEnclosure_long_le (T : SlopeBox) (D l r : ℝ) (hD : 0 < D)
    (ha : 0 < T.clipLength D l r) (hthin : 2*D*T.width ≤ T.clipLength D l r)
    (hs : |T.slope| ≤ 1) :
    (T.thinEnclosure D l r hD ha hthin).long ≤ 3*(r-l) := by
  exact (slope_rectangle_long_le _ _ _ _ _ _ _ hs).trans
    (mul_le_mul_of_nonneg_left (T.clipLength_le_strip D l r) (by norm_num))

theorem thinEnclosure_volume_le (T : SlopeBox) (D l r : ℝ) (hD : 0 < D)
    (ha : 0 < T.clipLength D l r) (hthin : 2*D*T.width ≤ T.clipLength D l r) :
    volume (T.thinEnclosure D l r hD ha hthin).carrier ≤
      ENNReal.ofReal (8*D^2*T.length*T.width) := by
  apply (volume_slopeRectangle_le _ _ _ _ _ _ _).trans
  apply ENNReal.ofReal_le_ofReal
  have h := mul_le_mul_of_nonneg_right (T.clipLength_le_dilation D l r)
    (show 0 ≤ 4*D*T.width by have := T.width_pos; positivity)
  nlinarith

theorem clipped_aperture_ge (T : SlopeBox) (D l r : ℝ) (_hD : 0 < D)
    (ha : 0 < T.clipLength D l r) :
    T.width/(12*T.length) ≤ (2*D*T.width)/(12*T.clipLength D l r) := by
  apply (div_le_div_iff₀ (by have := T.length_pos; positivity) (by positivity)).mpr
  have h := mul_le_mul_of_nonneg_left (T.clipLength_le_dilation D l r) T.width_pos.le
  nlinarith

theorem thinEnclosure_admissible (T : SlopeBox) (D l r : ℝ) (hD : 0 < D)
    (ha : 0 < T.clipLength D l r) (hthin : 2*D*T.width ≤ T.clipLength D l r)
    (hs : |T.slope| ≤ 1) (u : Plane → ℝ) (K δ : ℝ≥0) (E : Set (ℝ × ℝ))
    (hE : ∀ z ∈ E, z.1 ∈ Icc l r ∧ z ∈ T.radialDilation D)
    (hclose : ∀ z ∈ E, |u (planeCoordinates z)-T.slope| ≤ T.width/(12*T.length))
    (hlength : 300*(K:ℝ)*(r-l) ≤ 1)
    (harea : (δ:ℝ≥0∞)*ENNReal.ofReal (8*D^2*T.length*T.width) ≤ (volume.prod volume) E) :
    (T.thinEnclosure D l r hD ha hthin).Admissible (fun p => slopeDirection (u p)) K δ := by
  constructor
  · have h := mul_le_mul_of_nonneg_left (T.thinEnclosure_long_le D l r hD ha hthin hs)
      (by positivity : 0 ≤ 100*(K:ℝ))
    nlinarith
  · have hsub : planeCoordinates '' E ⊆
        (T.thinEnclosure D l r hD ha hthin).popularSet (fun p => slopeDirection (u p)) := by
      rintro _ ⟨z,hz,rfl⟩
      apply slopeRectangle_popular _ _ _ _ _ _ _ hs
      · exact T.mem_thinEnclosure D l r hD ha hthin z (hE z hz).1 (hE z hz).2
      · exact (hclose z hz).trans (T.clipped_aperture_ge D l r hD ha)
    calc
      _ ≤ (δ:ℝ≥0∞)*ENNReal.ofReal (8*D^2*T.length*T.width) :=
        mul_le_mul' le_rfl (T.thinEnclosure_volume_le D l r hD ha hthin)
      _ ≤ (volume.prod volume) E := harea
      _ = volume (planeCoordinates '' E) := (planeCoordinates_image_measure E).symm
      _ ≤ _ := measure_mono hsub

end LipschitzHilbert.SlopeBox

end

end OAI
