import OAI.Analysis.LipschitzHilbert.Geometry.LaceyLiGeometry
import Mathlib.MeasureTheory.Integral.MeanInequalities

namespace OAI

/-! Exact first and second moments of finite rectangle counts, in the
normalization of Lacey--Li's covering lemma (3.1)--(3.2). -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal NNReal
namespace LipschitzHilbert
variable {ι : Type*}

def rectangleCount (R : ι → Rectangle) (s : Finset ι) (x : Plane) : ℝ≥0∞ :=
  ∑ i∈s, (R i).carrier.indicator (fun _ => (1:ℝ≥0∞)) x

theorem rectangleCount_measurable (R : ι → Rectangle) (s : Finset ι) :
    Measurable (rectangleCount R s) :=
  Finset.measurable_sum _ (fun i _ => measurable_const.indicator (R i).measurableSet_carrier)

theorem rectangleCount_first_moment (R : ι → Rectangle) (s : Finset ι) :
    (∫⁻ x, rectangleCount R s x)=∑ i∈s, volume (R i).carrier := by
  unfold rectangleCount
  rw [lintegral_finsetSum _ (fun i _ => measurable_const.indicator (R i).measurableSet_carrier)]
  simp only [lintegral_indicator_fun_one (Rectangle.measurableSet_carrier _)]

theorem rectangleCount_second_moment (R : ι → Rectangle) (s : Finset ι) :
    (∫⁻ x, rectangleCount R s x^2)=∑ i∈s, ∑ j∈s, volume ((R i).carrier ∩ (R j).carrier) := by
  classical
  have he (x : Plane) : rectangleCount R s x^2=
      ∑ i∈s, ∑ j∈s, ((R i).carrier ∩ (R j).carrier).indicator (fun _ => (1:ℝ≥0∞)) x := by
    unfold rectangleCount
    rw [pow_two,Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hi : x∈(R i).carrier <;> by_cases hj : x∈(R j).carrier <;> simp [hi,hj]
  simp_rw [he]
  rw [lintegral_finsetSum _ (fun i _ => Finset.measurable_sum _ (fun j _ =>
    measurable_const.indicator ((R i).measurableSet_carrier.inter (R j).measurableSet_carrier)))]
  apply Finset.sum_congr rfl
  intro i _
  rw [lintegral_finsetSum _ (fun j _ =>
    measurable_const.indicator ((R i).measurableSet_carrier.inter (R j).measurableSet_carrier))]
  apply Finset.sum_congr rfl
  intro j _
  exact lintegral_indicator_fun_one ((R i).measurableSet_carrier.inter (R j).measurableSet_carrier)

theorem rectangleCount_first_moment_ne_top (R : ι → Rectangle) (s : Finset ι) :
    (∫⁻ x, rectangleCount R s x)≠∞ := by
  rw [rectangleCount_first_moment]
  exact ENNReal.sum_ne_top.mpr (fun i _ => (R i).volume_carrier_ne_top)

theorem rectangleCount_second_moment_ne_top (R : ι → Rectangle) (s : Finset ι) :
    (∫⁻ x, rectangleCount R s x^2)≠∞ := by
  rw [rectangleCount_second_moment]
  apply ENNReal.sum_ne_top.mpr
  intro i _
  apply ENNReal.sum_ne_top.mpr
  intro j _
  exact ne_top_of_le_ne_top (R i).volume_carrier_ne_top (measure_mono inter_subset_left)

theorem rectangleCount_pairing (R : ι → Rectangle) (s : Finset ι) (h : Plane → ℝ)
    (hh : AEStronglyMeasurable h volume) :
    (∫⁻ x, ‖h x‖ₑ*rectangleCount R s x)=∑ i∈s, ∫⁻ x in (R i).carrier, ‖h x‖ₑ := by
  classical
  have he (x : Plane) : ‖h x‖ₑ*rectangleCount R s x=
      ∑ i∈s, (R i).carrier.indicator (fun y => ‖h y‖ₑ) x := by
    unfold rectangleCount
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : x∈(R i).carrier <;> simp [hi]
  simp_rw [he]
  rw [lintegral_finsetSum' _ (fun i _ => hh.enorm.indicator (R i).measurableSet_carrier)]
  simp only [lintegral_indicator (Rectangle.measurableSet_carrier _)]

theorem rectangleCount_pairing_sq_le (R : ι → Rectangle) (s : Finset ι) (h : Plane → ℝ)
    (hh : AEStronglyMeasurable h volume) :
    (∫⁻ x, ‖h x‖ₑ*rectangleCount R s x)^2 ≤
      squareIntegral volume h*(∫⁻ x, rectangleCount R s x^2) := by
  have hc := ENNReal.lintegral_mul_le_Lp_mul_Lq volume Real.HolderConjugate.two_two
    hh.enorm (rectangleCount_measurable R s).aemeasurable
  have hroot (a : ℝ≥0∞) : (a^(1/2:ℝ))^2=a := by
    rw [←ENNReal.rpow_mul_natCast]
    norm_num
  have hp := pow_le_pow_left' hc 2
  rw [mul_pow,hroot,hroot] at hp
  simpa only [ENNReal.rpow_two,Pi.mul_apply,squareIntegral] using hp

end LipschitzHilbert

end

end OAI
