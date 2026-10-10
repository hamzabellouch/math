import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.MeasureBounds

namespace OAI

namespace RieszRectifiability

noncomputable section

open Filter Metric Topology

theorem exists_continuous_uniform_limit_of_geometric_steps {X : Type*} [TopologicalSpace X]
    {d : ℕ} (F : ℕ → X → Ambient d) (C q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hcontinuous : ∀ t, Continuous (F t))
    (hstep : ∀ t x, dist (F t x) (F (t + 1) x) ≤ C * q ^ t) :
    ∃ f : X → Ambient d, Continuous f ∧ TendstoUniformly F f atTop ∧
      ∀ t x, dist (F t x) (f x) ≤ C * q ^ t / (1 - q) := by
  have hex : ∀ x, ∃ y, Tendsto (fun t => F t x) atTop (𝓝 y) := by
    intro x
    exact cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric q C hq1 (fun t => hstep t x))
  choose f hf using hex
  have hbound : ∀ t x, dist (F t x) (f x) ≤ C * q ^ t / (1 - q) := by
    intro t x
    exact dist_le_of_le_geometric_of_tendsto q C hq1 (fun s => hstep s x) (hf x) t
  have hdecay : Tendsto (fun t : ℕ => C * q ^ t / (1 - q)) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_div] using!
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul C).div_const (1 - q)
  have hlimit : TendstoUniformly F f atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro δ hδ
    have hevent : ∀ᶠ t in atTop, C * q ^ t / (1 - q) < δ :=
      hdecay.eventually (gt_mem_nhds hδ)
    filter_upwards [hevent] with t ht x
    rw [dist_comm]
    exact (hbound t x).trans_lt ht
  exact ⟨f, hlimit.continuous (Filter.Eventually.of_forall hcontinuous).frequently, hlimit, hbound⟩

end

end RieszRectifiability

end OAI
