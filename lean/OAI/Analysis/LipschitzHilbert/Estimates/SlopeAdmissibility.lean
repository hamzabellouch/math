import OAI.Analysis.LipschitzHilbert.Geometry.SlopeRectangle
import OAI.Analysis.LipschitzHilbert.Geometry.SlopeDirection

namespace OAI

/-! Admissibility of the actual thin enclosing rectangle from a slope
popularity witness, with an explicit short horizontal localization. -/

noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal
namespace LipschitzHilbert

theorem slopeRectangle_popular (c : ℝ × ℝ) (s a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a) (hs : |s| ≤ 1)
    (u : Plane → ℝ) (z : Plane)
    (hz : z ∈ (slopeRectangle c s a b ha hb hba).carrier)
    (hu : |u z-s| ≤ b/(12*a)) :
    z ∈ (slopeRectangle c s a b ha hb hba).popularSet (fun p => slopeDirection (u p)) := by
  let R := slopeRectangle c s a b ha hb hba
  have hl : 0 < R.long := R.short_pos.trans_le R.short_le_long
  have hhalf : R.short/(2*R.long) ≤ (1:ℝ)/2 := by
    apply (div_le_iff₀ (mul_pos (by norm_num) hl)).mpr
    linarith [R.short_le_long]
  refine ⟨hz,?_⟩
  change Real.cos (R.short/(2*R.long)) ≤ inner ℝ (slopeDirection (u z)) (slopeDirection s)
  exact cos_le_inner_slopeDirection (u z) s _ (hhalf.trans (by linarith [Real.two_le_pi]))
    (hu.trans (slope_rectangle_aperture_ge c s a b ha hb hba hs))

theorem slopeRectangle_admissible (c : ℝ × ℝ) (s a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a) (hs : |s| ≤ 1)
    (u : Plane → ℝ) (K δ : ℝ≥0) (E : Set Plane)
    (hE : E ⊆ (slopeRectangle c s a b ha hb hba).carrier)
    (hclose : ∀ z ∈ E, |u z-s| ≤ b/(12*a))
    (hlength : 300*(K:ℝ)*a ≤ 1)
    (harea : (δ:ℝ≥0∞)*ENNReal.ofReal (2*a*b) ≤ volume E) :
    (slopeRectangle c s a b ha hb hba).Admissible (fun p => slopeDirection (u p)) K δ := by
  constructor
  · have h := mul_le_mul_of_nonneg_left (slope_rectangle_long_le c s a b ha hb hba hs)
      (by positivity : 0 ≤ 100*(K:ℝ))
    nlinarith
  · calc
      _ ≤ (δ:ℝ≥0∞)*ENNReal.ofReal (2*a*b) := mul_le_mul' le_rfl
        (volume_slopeRectangle_le c s a b ha hb hba)
      _ ≤ volume E := harea
      _ ≤ _ := measure_mono (fun z hz => slopeRectangle_popular c s a b ha hb hba hs u z
        (hE hz) (hclose z hz))

end LipschitzHilbert

end

end OAI
