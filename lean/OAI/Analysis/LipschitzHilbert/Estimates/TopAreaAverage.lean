import OAI.Analysis.LipschitzHilbert.Estimates.TopDyadicDomination

namespace OAI

/-! Actual normalized intersection averages and top-area weights. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators
namespace LipschitzHilbert.SlopeBox

def area (T : SlopeBox) : ℝ := T.length*T.width

theorem area_pos (T : SlopeBox) : 0 < T.area := mul_pos T.length_pos T.width_pos

def areaWeight (T : SlopeBox) : ℝ≥0 := ⟨T.area,T.area_pos.le⟩

@[simp] theorem coe_areaWeight (T : SlopeBox) : (T.areaWeight:ℝ) = T.area := rfl

@[simp] theorem ennreal_areaWeight (T : SlopeBox) : (T.areaWeight:ℝ≥0∞) =
    ENNReal.ofReal T.area := ENNReal.coe_nnreal_eq T.areaWeight

def dilationAverage (T : SlopeBox) (D : ℝ) (Q : Set (ℝ × ℝ)) : ℝ :=
  (volume.prod volume).real (Q ∩ T.radialDilation D)/(8*D^2*T.length*T.width)

theorem dilationAverage_nonneg (T : SlopeBox) (D : ℝ) (Q : Set (ℝ × ℝ)) :
    0 ≤ T.dilationAverage D Q := by
  unfold dilationAverage
  have := T.length_pos
  have := T.width_pos
  positivity

theorem dilationAverage_normalized (T : SlopeBox) (D : ℝ) (hD : 0 < D)
    (Q : Set (ℝ × ℝ)) (hQfin : (volume.prod volume) Q ≠ ∞) :
    ENNReal.ofReal (T.dilationAverage D Q*(8*D^2*T.length*T.width)) =
      (volume.prod volume) (Q ∩ T.radialDilation D) := by
  have hB : 8*D^2*T.length*T.width ≠ 0 := by
    have := T.length_pos
    have := T.width_pos
    positivity
  have hi : (volume.prod volume) (Q ∩ T.radialDilation D) ≠ ∞ :=
    ne_top_of_le_ne_top hQfin (measure_mono inter_subset_left)
  rw [dilationAverage, div_mul_cancel₀ _ hB]
  exact ENNReal.ofReal_toReal hi

theorem dilation_intersection_eq (T : SlopeBox) (D : ℝ) (hD : 0 < D)
    (Q : Set (ℝ × ℝ)) (hQfin : (volume.prod volume) Q ≠ ∞) :
    (volume.prod volume) (Q ∩ T.radialDilation D) =
      ENNReal.ofReal (8*D^2)*((T.areaWeight:ℝ≥0∞)*ENNReal.ofReal (T.dilationAverage D Q)) := by
  rw [ennreal_areaWeight, ← ENNReal.ofReal_mul T.area_pos.le,
    ← ENNReal.ofReal_mul (by positivity), ← T.dilationAverage_normalized D hD Q hQfin]
  congr 1
  unfold area
  ring

theorem sum_dilation_intersection_eq {ι : Type*} [Fintype ι]
    (T : ι → SlopeBox) (D : ℝ) (hD : 0 < D)
    (Q : Set (ℝ × ℝ)) (hQfin : (volume.prod volume) Q ≠ ∞) :
    (∑ i, (volume.prod volume) (Q ∩ (T i).radialDilation D)) =
      ENNReal.ofReal (8*D^2)*∑ i, ((T i).areaWeight:ℝ≥0∞)*ENNReal.ofReal ((T i).dilationAverage D Q) := by
  simp only [dilation_intersection_eq _ D hD Q hQfin, Finset.mul_sum]

end LipschitzHilbert.SlopeBox

end

end OAI
