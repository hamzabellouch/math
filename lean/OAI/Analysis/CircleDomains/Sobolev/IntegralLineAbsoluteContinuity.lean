import Mathlib.MeasureTheory.Function.AbsolutelyContinuous

namespace OAI

/-! A linewise integral bound yields actual absolute continuity, without
first choosing a measurable representative for the bounded potential. -/

open Set Filter MeasureTheory
open scoped Topology

namespace CircleDomainRigidity

variable {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]

theorem absolutelyContinuousOnInterval_of_dist_le
    {f : ℝ → X} {g : ℝ → Y} {a b : ℝ}
    (hg : AbsolutelyContinuousOnInterval g a b)
    (hfg : ∀x ∈ uIcc a b, ∀y ∈ uIcc a b, dist (f x) (f y) ≤ dist (g x) (g y)) :
    AbsolutelyContinuousOnInterval f a b := by
  rw [absolutelyContinuousOnInterval_iff] at hg ⊢
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := hg ε hε
  refine ⟨δ, hδ, fun E hE hlen => ?_⟩
  apply lt_of_le_of_lt _ (h E hE hlen)
  exact Finset.sum_le_sum fun i hi => hfg _ (hE.1 i hi).1 _ (hE.1 i hi).2

theorem absolutelyContinuousOnInterval_of_integral_bound
    {f : ℝ → X} {g : ℝ → ℝ} {a b : ℝ}
    (hg : IntervalIntegrable g volume a b)
    (hfg : ∀x ∈ uIcc a b, ∀y ∈ uIcc a b,
      dist (f x) (f y) ≤ ∫t in uIoc x y, g t) :
    AbsolutelyContinuousOnInterval f a b := by
  apply absolutelyContinuousOnInterval_of_dist_le
    (hg.absolutelyContinuousOnInterval_intervalIntegral (left_mem_uIcc))
  intro x hx y hy
  apply (hfg x hx y hy).trans
  rw [Real.dist_eq, intervalIntegral.integral_interval_sub_left
    (hg.mono_set' (uIoc_subset_uIoc_of_uIcc_subset_uIcc (uIcc_subset_uIcc left_mem_uIcc hx)))
    (hg.mono_set' (uIoc_subset_uIoc_of_uIcc_subset_uIcc (uIcc_subset_uIcc left_mem_uIcc hy))),
    intervalIntegral.abs_intervalIntegral_eq]
  simpa only [uIoc_comm y x] using (le_abs_self (∫t in uIoc x y, g t))

end CircleDomainRigidity

end OAI
