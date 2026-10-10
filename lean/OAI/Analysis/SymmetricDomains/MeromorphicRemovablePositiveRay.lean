import Mathlib
import OAI.Analysis.SymmetricDomains.CompactPeakRatio

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Metric
open scoped Topology

theorem meromorphic_no_pole_of_positive_ray_bound {f : ℂ → ℂ}
    (hf : MeromorphicAt f 0) {r B : ℝ} (hr : 0 < r)
    (hb : ∀ t : ℝ, 0 < t → t < r → ‖f t‖ ≤ B) :
    ∃ c : ℂ, Tendsto f (𝓝[≠] 0) (𝓝 c) := by
  apply tendsto_nhds_of_meromorphicOrderAt_nonneg hf
  by_contra h
  have hp := tendsto_cobounded_of_meromorphicOrderAt_neg (lt_of_not_ge h)
  let u : ℕ → ℝ := fun n => 1 / (n+1)
  have hu : Tendsto u atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have huc : Tendsto (fun n => (u n : ℂ)) atTop (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_,Eventually.of_forall ?_⟩
    · exact_mod_cast Complex.continuous_ofReal.continuousAt.tendsto.comp hu
    · intro n
      simp only [mem_compl_iff, mem_singleton_iff, Complex.ofReal_eq_zero]
      exact ne_of_gt (by dsimp [u]; positivity)
  have hlarge := ((tendsto_norm_atTop_iff_cobounded.mpr hp).comp huc).eventually
    (eventually_gt_atTop (B+1))
  have hsmall := hu.eventually (gt_mem_nhds hr)
  obtain ⟨n,hn₁,hn₂⟩ := (hlarge.and hsmall).exists
  have hh := hb (u n) (by dsimp [u]; positivity) hn₂
  change B + 1 < ‖f (u n : ℂ)‖ at hn₁
  linarith

theorem meromorphic_removable_of_positive_ray_bound {f : ℂ → ℂ}
    {U : Set ℂ} (hU : IsOpen U) (h0 : (0 : ℂ) ∈ U)
    (hf : AnalyticOnNhd ℂ f (U \ {0})) (hm : MeromorphicAt f 0)
    {r B : ℝ} (hr : 0 < r)
    (hb : ∀ t : ℝ, 0 < t → t < r → ‖f t‖ ≤ B) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g U ∧ EqOn g f (U \ {0}) := by
  classical
  obtain ⟨c,hc⟩ := meromorphic_no_pole_of_positive_ray_bound hm hr hb
  let g := Function.update f 0 c
  have heq : ∀ x : ℂ, x ≠ 0 → g x = f x := by
    intro x hx
    simp [g, Function.update_of_ne hx]
  have hag : ∀ x ∈ U \ {0}, AnalyticAt ℂ g x := by
    intro x hx
    apply (hf x hx).congr
    filter_upwards [isOpen_compl_singleton.mem_nhds hx.2] with y hy
    exact (heq y hy).symm
  refine ⟨g,?_,fun x hx => heq x hx.2⟩
  intro x hx
  by_cases hx0 : x = 0
  · subst x
    have hgc : ContinuousAt g 0 := by
      rw [← continuousWithinAt_compl_self]
      have hg0 : g 0 = c := by simp [g]
      change Tendsto g (𝓝[≠] 0) (𝓝 (g 0))
      rw [hg0]
      apply hc.congr'
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact (heq y hy).symm
    apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt _ hgc
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (hU.mem_nhds h0)] with y hy hyU
    exact (hag y ⟨hyU,hy⟩).differentiableAt
  · exact hag x ⟨hx,hx0⟩

end Release061

end

end OAI
