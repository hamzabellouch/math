import OAI.MeasureTheory.Falconer.Geometry.Bins
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Algebra.Order.Floor.Ring

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set
open scoped ENNReal

noncomputable def binL2Norm (μ : Measure ℝ) (w : ℝ) : ℝ≥0∞ :=
  (∑' j : ℤ, (μ (realBin w j))^2)^(1/2 : ℝ)

 theorem ennreal_offset_cauchy (a b : ℤ → ℝ≥0∞) (h : ℤ) :
    (∑' j : ℤ, a j*b (j-h)) ≤
      (∑' j : ℤ, (a j)^2)^(1/2 : ℝ) * (∑' j : ℤ, (b j)^2)^(1/2 : ℝ) := by
  have hpq : (2:ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]; norm_num
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq (Measure.count : Measure ℤ) hpq
    (measurable_of_countable a).aemeasurable
    (measurable_of_countable (fun j => b (j-h))).aemeasurable
  simp only [lintegral_count, ENNReal.rpow_two] at hh
  have he : (∑' j : ℤ, (b (j-h))^2) = ∑' j : ℤ, (b j)^2 :=
    (Equiv.subRight h).tsum_eq (fun j => (b j)^2)
  simpa only [one_div, he, Pi.mul_apply] using hh

 theorem realBin_cover {w : ℝ} (hw : 0 < w) (x : ℝ) :
    x ∈ realBin w ⌊x/w⌋ := by
  constructor
  · exact (le_div_iff₀ hw).mp (Int.floor_le (x/w))
  · simpa only [Int.cast_add,Int.cast_one] using
      (div_lt_iff₀ hw).mp (Int.lt_floor_add_one (x/w))

 theorem offset_rectangles_mass_le (μ ν : Measure ℝ) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (w : ℝ) (h : ℤ) :
    (μ.prod ν) (⋃ j : ℤ, realBin w j ×ˢ realBin w (j-h)) ≤
      binL2Norm μ w * binL2Norm ν w := by
  apply (measure_iUnion_le _).trans
  simp only [Measure.prod_prod]
  exact ennreal_offset_cauchy (fun j => μ (realBin w j)) (fun j => ν (realBin w j)) h

 theorem finite_offset_rectangles_mass_le (μ ν : Measure ℝ) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (w : ℝ) (H : Finset ℤ) :
    (μ.prod ν) (⋃ h ∈ H, ⋃ j : ℤ, realBin w j ×ˢ realBin w (j-h)) ≤
      (H.card : ℝ≥0∞) * (binL2Norm μ w * binL2Norm ν w) := by
  calc
    _ ≤ ∑ h ∈ H, (μ.prod ν) (⋃ j : ℤ, realBin w j ×ˢ realBin w (j-h)) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ _h ∈ H, binL2Norm μ w * binL2Norm ν w :=
      Finset.sum_le_sum (fun h _ => offset_rectangles_mass_le μ ν w h)
    _ = _ := by simp

end PlanarFalconer

end OAI
