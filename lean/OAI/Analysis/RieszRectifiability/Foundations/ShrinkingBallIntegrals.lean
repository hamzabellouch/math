import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.KernelBasic

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

theorem measure_ball_tendsto_zero_of_growth {d : ℕ} (n : ℕ) (hn : 0 < n)
    (μ : Measure (Ambient d)) (C : ℝ) (hg : GlobalUpperGrowth n C μ)
    (x : Ambient d) (r : ℕ → ℝ) (hr : ∀ j, 0 < r j) (hr0 : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun j => μ (ball x (r j))) atTop (𝓝 0) := by
  have hbound : Tendsto (fun j => ENNReal.ofReal (C * r j ^ n)) atTop (𝓝 0) := by
    simpa only [zero_pow hn.ne', mul_zero, ENNReal.ofReal_zero] using!
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp ((hr0.pow n).const_mul C)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound
    (fun _ => bot_le) (fun j => hg.2 x (r j) (hr j))

theorem local_integral_tendsto_zero_on_shrinking_balls {d : ℕ}
    (μ : Measure (Ambient d)) (f : Ambient d → ℝ) (x : Ambient d) (R : ℝ) (hR : 0 < R)
    (hi : IntegrableOn f (ball x R) μ) (r : ℕ → ℝ) (hr0 : Tendsto r atTop (𝓝 0))
    (hmass : Tendsto (fun j => μ (ball x (r j))) atTop (𝓝 0)) :
    Tendsto (fun j => ∫ y in ball x (r j), f y ∂μ) atTop (𝓝 0) := by
  have hrestrict : Tendsto (fun j => (μ.restrict (ball x R)) (ball x (r j))) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmass
      (fun _ => bot_le) (fun j => Measure.restrict_le_self (ball x (r j)))
  have hlim := hi.tendsto_setIntegral_nhds_zero hrestrict
  apply hlim.congr'
  filter_upwards [hr0.eventually (gt_mem_nhds hR)] with j hj
  rw [Measure.restrict_restrict measurableSet_ball,
    inter_eq_left.mpr (ball_subset_ball hj.le)]

end

end RieszRectifiability

end OAI
