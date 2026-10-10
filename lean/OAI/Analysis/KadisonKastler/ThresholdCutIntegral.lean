import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Real.Sqrt

namespace OAI

/-! # Averaging finite spectral threshold cuts

Two spectral values are separated by a threshold on an interval of
length equal to their distance. Finite weighted sums give the exact
average cut energy and its Cauchy--Schwarz bound.
-/

namespace KadisonKastler

open MeasureTheory
open scoped BigOperators

noncomputable section

def thresholdDifference (x y t : ℝ) : ℝ :=
  (if t < x then 1 else 0) - (if t < y then 1 else 0)

theorem thresholdDifference_sq (x y t : ℝ) :
    thresholdDifference x y t ^ 2 =
      (Set.Ico (min x y) (max x y)).indicator (fun _ => (1 : ℝ)) t := by
  by_cases hxy : x ≤ y
  · rw [min_eq_left hxy,max_eq_right hxy]
    by_cases htx : t < x
    · have hty : t < y := htx.trans_le hxy
      simp [thresholdDifference,htx,hty,Set.mem_Ico,not_le.mpr htx]
    · by_cases hty : t < y
      · simp [thresholdDifference,htx,hty,Set.mem_Ico,le_of_not_gt htx]
      · simp [thresholdDifference,htx,hty,Set.mem_Ico]
  · have hyx : y ≤ x := le_of_not_ge hxy
    rw [min_eq_right hyx,max_eq_left hyx]
    by_cases hty : t < y
    · have htx : t < x := hty.trans_le hyx
      simp [thresholdDifference,htx,hty,Set.mem_Ico,not_le.mpr hty]
    · by_cases htx : t < x
      · simp [thresholdDifference,htx,hty,Set.mem_Ico,le_of_not_gt hty]
      · simp [thresholdDifference,htx,hty,Set.mem_Ico]

theorem thresholdDifference_sq_integrable (x y : ℝ) :
    Integrable (fun t => thresholdDifference x y t ^ 2) := by
  simp_rw [thresholdDifference_sq]
  exact (integrable_indicator_iff measurableSet_Ico).mpr
    (integrableOn_const (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top))

theorem integral_thresholdDifference_sq (x y : ℝ) :
    (∫ t, thresholdDifference x y t ^ 2) = |x - y| := by
  simp_rw [thresholdDifference_sq]
  rw [integral_indicator_const (1 : ℝ) measurableSet_Ico]
  simp only [smul_eq_mul,mul_one,Measure.real,Real.volume_Ico,
    ENNReal.toReal_ofReal (sub_nonneg.mpr (min_le_max))]
  exact (max_sub_min_eq_abs x y).trans (abs_sub_comm y x)

theorem integral_weighted_thresholdDifference_sq {ι : Type*} (s : Finset ι)
    (x y w : ι → ℝ) :
    (∫ t, ∑ i ∈ s, w i * thresholdDifference (x i) (y i) t ^ 2) =
      ∑ i ∈ s, w i * |x i - y i| := by
  rw [integral_finsetSum s (fun i _ => (thresholdDifference_sq_integrable (x i) (y i)).const_mul _)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_const_mul,integral_thresholdDifference_sq]

theorem weighted_threshold_energy_le {ι : Type*} (s : Finset ι)
    (x y w : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∫ t, ∑ i ∈ s, w i * thresholdDifference (x i) (y i) t ^ 2) ≤
      Real.sqrt (∑ i ∈ s, w i * (x i - y i) ^ 2) * Real.sqrt (∑ i ∈ s, w i) := by
  rw [integral_weighted_thresholdDifference_sq]
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt s
    (fun i => Real.sqrt (w i) * |x i-y i|) (fun i => Real.sqrt (w i))
  have hleft (i : ι) (hi : i ∈ s) :
      (Real.sqrt (w i) * |x i-y i|) * Real.sqrt (w i) = w i * |x i-y i| := by
    calc
      _ = Real.sqrt (w i) ^ 2 * |x i-y i| := by ring
      _ = _ := by rw [Real.sq_sqrt (hw i hi)]
  have hsq (i : ι) (hi : i ∈ s) :
      (Real.sqrt (w i) * |x i-y i|) ^ 2 = w i * (x i-y i) ^ 2 := by
    rw [mul_pow,Real.sq_sqrt (hw i hi),sq_abs]
  have hw' : (∑ i ∈ s, Real.sqrt (w i) ^ 2) = ∑ i ∈ s, w i :=
    Finset.sum_congr rfl (fun i hi => Real.sq_sqrt (hw i hi))
  rw [Finset.sum_congr rfl hleft,Finset.sum_congr rfl hsq,hw'] at hcs
  exact hcs

end

end KadisonKastler

end OAI
