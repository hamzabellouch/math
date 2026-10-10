import OAI.Analysis.IrrationalRotation.Analysis.FejerKernel
import Mathlib.MeasureTheory.Integral.PeakFunction

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Invariant233.Fejer

theorem kernel_tendstoUniformlyOn_compl
    (u : Set Circle) (hu : IsOpen u) (h0 : (0 : Circle) ∈ u) :
    TendstoUniformlyOn (fun n : ℕ => kernel (n + 1)) 0 atTop uᶜ := by
  obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.mp hu 0 h0
  have hn : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hb : Tendsto (fun n : ℕ => (1 / (4 * η ^ 2)) / (n + 1 : ℕ))
      atTop (𝓝 (0 : ℝ)) := tendsto_const_nhds.div_atTop hn
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [hb.eventually (gt_mem_nhds hε)] with n hnε
  intro x hx
  have hdist : η ≤ dist x 0 := by
    by_contra h
    exact hx (hball (show x ∈ Metric.ball 0 η from lt_of_not_ge h))
  have hk := kernel_le_of_distance_ge (n + 1) (Nat.succ_ne_zero n) hη x hdist
  have heq : 1 / (4 * (n + 1 : ℕ) * η ^ 2) =
      (1 / (4 * η ^ 2)) / (n + 1 : ℕ) := by ring
  rw [heq] at hk
  simpa only [Pi.zero_apply, dist_zero_left, Real.norm_eq_abs,
    abs_of_nonneg (kernel_nonneg (n + 1) x)] using hk.trans_lt hnε

theorem tendsto_integral_kernel_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {g : Circle → E} (hg : Integrable g AddCircle.haarAddCircle)
    (h0 : ContinuousAt g 0) :
    Tendsto (fun n : ℕ => ∫ t, kernel (n + 1) t • g t ∂AddCircle.haarAddCircle)
      atTop (𝓝 (g 0)) := by
  apply tendsto_integral_peak_smul_of_integrable_of_tendsto
    (t := Set.univ) MeasurableSet.univ (by simp) (measure_ne_top _ _)
  · exact Eventually.of_forall fun n t => kernel_nonneg (n + 1) t
  · exact kernel_tendstoUniformlyOn_compl
  · have heq : (fun n : ℕ => ∫ t in Set.univ, kernel (n + 1) t
        ∂AddCircle.haarAddCircle) = fun _ => (1 : ℝ) := by
      funext n
      rw [MeasureTheory.setIntegral_univ, integral_kernel (n + 1) (Nat.succ_ne_zero n)]
    rw [heq]
    exact tendsto_const_nhds
  · exact Eventually.of_forall fun n => (continuous_kernel (n + 1)).aestronglyMeasurable
  · exact hg
  · exact h0

theorem tendsto_integral_kernel_smul_of_continuous
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {g : Circle → E} (hg : Continuous g) :
    Tendsto (fun n : ℕ => ∫ t, kernel (n + 1) t • g t ∂AddCircle.haarAddCircle)
      atTop (𝓝 (g 0)) :=
  tendsto_integral_kernel_smul
    (hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace g)) hg.continuousAt

end Invariant233.Fejer

end

end OAI
