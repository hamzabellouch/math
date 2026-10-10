import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace OAI

open MeasureTheory Set

namespace MarkovSuperreflexivity

noncomputable def lowerPowerKernel (s r t : ℝ) : ℝ :=
  if 0 < t ∧ t < r then t ^ (s - 1) else 0

noncomputable def upperPowerKernel (s r t : ℝ) : ℝ :=
  if 0 < t ∧ r ≤ t then t ^ (-s - 1) else 0

theorem lowerPowerKernel_eq_indicator (s r : ℝ) :
    lowerPowerKernel s r =
      (Ioo (0 : ℝ) r).indicator (fun t => t ^ (s - 1)) := by
  funext t
  simp only [lowerPowerKernel, Set.indicator, Set.mem_Ioo]

theorem upperPowerKernel_eq_indicator {s r : ℝ} (hr : 0 < r) :
    upperPowerKernel s r =
      (Ici r).indicator (fun t => t ^ (-s - 1)) := by
  funext t
  by_cases hrt : r ≤ t
  · have ht : 0 < t := hr.trans_le hrt
    simp [upperPowerKernel, Set.indicator, hrt, ht]
  · simp [upperPowerKernel, Set.indicator, hrt]

theorem integrable_lowerPowerKernel {s r : ℝ} (hs : 0 < s) (hr : 0 ≤ r) :
    Integrable (lowerPowerKernel s r) := by
  rw [lowerPowerKernel_eq_indicator]
  have hp : -1 < s - 1 := by linarith
  have hi : IntervalIntegrable (fun t : ℝ => t ^ (s - 1)) volume 0 r :=
    intervalIntegral.intervalIntegrable_rpow' hp
  exact ((intervalIntegrable_iff_integrableOn_Ioo_of_le hr).mp hi).integrable_indicator
    measurableSet_Ioo

theorem integral_lowerPowerKernel {s r : ℝ} (hs : 0 < s) (hr : 0 ≤ r) :
    (∫ t, lowerPowerKernel s r t) = r ^ s / s := by
  rw [lowerPowerKernel_eq_indicator, integral_indicator measurableSet_Ioo,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hr]
  simpa only [sub_add_cancel, Real.zero_rpow hs.ne', sub_zero] using
    (_root_.integral_rpow (a := 0) (b := r) (r := s - 1)
      (Or.inl (by linarith : -1 < s - 1)))

theorem integrable_upperPowerKernel {s r : ℝ} (hs : 0 < s) (hr : 0 < r) :
    Integrable (upperPowerKernel s r) := by
  rw [upperPowerKernel_eq_indicator hr]
  have hi : IntegrableOn (fun t : ℝ => t ^ (-s - 1)) (Ioi r) :=
    integrableOn_Ioi_rpow_of_lt (by linarith : -s - 1 < -1) hr
  exact ((integrableOn_Ici_iff_integrableOn_Ioi
    (f := fun t : ℝ => t ^ (-s - 1)) (b := r) (by finiteness)).mpr hi).integrable_indicator
    measurableSet_Ici

theorem integral_upperPowerKernel {s r : ℝ} (hs : 0 < s) (hr : 0 < r) :
    (∫ t, upperPowerKernel s r t) = r ^ (-s) / s := by
  rw [upperPowerKernel_eq_indicator hr, integral_indicator measurableSet_Ici,
    integral_Ici_eq_integral_Ioi]
  simpa only [sub_add_cancel, neg_div_neg_eq] using
    (integral_Ioi_rpow_of_lt (a := -s - 1) (c := r)
      (by linarith : -s - 1 < -1) hr)

end MarkovSuperreflexivity

end OAI
