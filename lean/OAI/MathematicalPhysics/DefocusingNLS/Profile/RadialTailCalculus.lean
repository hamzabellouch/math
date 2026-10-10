import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Group.Integral

namespace OAI

/-! Differentiation and translation of absolutely convergent backward tails. -/

open Set Filter MeasureTheory
namespace DefocusingNLS

theorem radial_tail_hasDerivAt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : ℝ → E)
    (hf : Continuous f) (a t : ℝ) (hat : a < t)
    (hi : IntegrableOn f (Ioi a)) :
    HasDerivAt (fun r => ∫ s in Ioi r, f s) (-f t) t := by
  have hd := (intervalIntegral.integral_hasDerivAt_right
    (hf.intervalIntegrable a t) hf.stronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt).const_sub
      (∫ s in Ioi a, f s)
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hat] with r hr
  have he := intervalIntegral.integral_interval_add_Ioi hi
    (hi.mono_set (Ioi_subset_Ioi hr.le))
  exact eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using he)

theorem radial_tail_translate {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℝ → E) (t : ℝ) :
    (∫ u in Ioi (0 : ℝ), f (t+u)) = ∫ s in Ioi t, f s := by
  have he := integral_add_left_eq_self (μ := volume) (fun s => (Ioi t).indicator f s) t
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
  convert he using 1
  apply integral_congr_ae
  exact Eventually.of_forall (fun u => by
    simp only [indicator_apply, mem_Ioi]
    split_ifs <;> simp_all
    linarith)

end DefocusingNLS

end OAI
