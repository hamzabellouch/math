import OAI.Analysis.LipschitzHilbert.Geometry.RectangleCountingEnergy

namespace OAI

/-! The analytic reduction in Lacey--Li, Chapter 3: the covering and
intersection estimates (3.1)--(3.2) imply the weak estimate for the
selected high-average family. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal NNReal
namespace LipschitzHilbert
variable {ι : Type*}

namespace Rectangle

theorem average_mul_volume (R : Rectangle) (h : Plane → ℝ) :
    R.average h*volume R.carrier=∫⁻ x in R.carrier, ‖h x‖ₑ := by
  unfold average
  rw [mul_right_comm,ENNReal.inv_mul_cancel R.volume_carrier_pos.ne' R.volume_carrier_ne_top,one_mul]

theorem high_average_integral (R : Rectangle) (h : Plane → ℝ) (t : ℝ≥0∞)
    (ht : t≤R.average h) : t*volume R.carrier≤∫⁻ x in R.carrier, ‖h x‖ₑ := by
  calc
    _ ≤ R.average h*volume R.carrier := mul_le_mul' ht le_rfl
    _ = _ := R.average_mul_volume h

end Rectangle

theorem selected_area_pairing_bound (R : ι → Rectangle) (s : Finset ι)
    (h : Plane → ℝ) (hh : AEStronglyMeasurable h volume) (t : ℝ≥0∞)
    (hhigh : ∀ i∈s, t≤(R i).average h) :
    t*(∑ i∈s,volume (R i).carrier)≤∫⁻ x, ‖h x‖ₑ*rectangleCount R s x := by
  rw [rectangleCount_pairing R s h hh,Finset.mul_sum]
  exact Finset.sum_le_sum (fun i hi => (R i).high_average_integral h t (hhigh i hi))

theorem selected_area_from_overlap (R : ι → Rectangle) (s : Finset ι)
    (h : Plane → ℝ) (hh : AEStronglyMeasurable h volume) (t D : ℝ≥0∞)
    (hhigh : ∀ i∈s, t≤(R i).average h)
    (hoverlap : (∫⁻ x, rectangleCount R s x^2)≤D*(∑ i∈s,volume (R i).carrier)) :
    t^2*(∑ i∈s,volume (R i).carrier)≤D*squareIntegral volume h := by
  let A := ∑ i∈s, volume (R i).carrier
  by_cases hA : A=0
  · change t^2*A≤_
    rw [hA,mul_zero]
    exact zero_le
  have hAtop : A≠∞ := ENNReal.sum_ne_top.mpr (fun i _ => (R i).volume_carrier_ne_top)
  have hpair := selected_area_pairing_bound R s h hh t hhigh
  have hsq := (pow_le_pow_left' hpair 2).trans (rectangleCount_pairing_sq_le R s h hh)
  have hm := mul_le_mul' (le_refl (squareIntegral volume h)) hoverlap
  have hall : A*(t^2*A)≤A*(D*squareIntegral volume h) := by
    calc
      _ = (t*A)^2 := by ring
      _ ≤ squareIntegral volume h*(∫⁻ x, rectangleCount R s x^2) := hsq
      _ ≤ squareIntegral volume h*(D*A) := hm
      _ = _ := by ring
  exact (ENNReal.mul_le_mul_iff_right hA hAtop).mp hall

theorem covering_weak_bound (R : ι → Rectangle) (s : Finset ι) (U : Set Plane)
    (h : Plane → ℝ) (hh : AEStronglyMeasurable h volume) (t B D : ℝ≥0∞)
    (hhigh : ∀ i∈s, t≤(R i).average h)
    (hcover : volume U≤B*(∑ i∈s,volume (R i).carrier))
    (hoverlap : (∫⁻ x, rectangleCount R s x^2)≤D*(∑ i∈s,volume (R i).carrier)) :
    t^2*volume U≤B*D*squareIntegral volume h := by
  calc
    _ ≤ t^2*(B*(∑ i∈s,volume (R i).carrier)) := mul_le_mul' le_rfl hcover
    _ = B*(t^2*(∑ i∈s,volume (R i).carrier)) := by ring
    _ ≤ B*(D*squareIntegral volume h) :=
      mul_le_mul' le_rfl (selected_area_from_overlap R s h hh t D hhigh hoverlap)
    _ = _ := by ring

end LipschitzHilbert

end

end OAI
