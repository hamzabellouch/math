import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.UniformSpace.UniformApproximation

namespace OAI

/-! # Limits of contracting boundary trajectories

Polynomial times exponential decay is summable. Metric trajectories with a
common increment bound converge uniformly, with a common tail bound and compact
normalized shadow. Asymptotic representatives of a quotient point have equal
limits and determine a continuous boundary map.
-/

noncomputable section

namespace PolycyclicRecognition

open Filter Metric
open scoped Topology

/-- The summable increment profile appearing in the ray-boundary proof. -/
theorem summable_polynomial_exp_decay (C : ℝ) (M : ℕ) {c : ℝ} (hc : 0 < c) :
    Summable (fun n : ℕ => C * (1 + (n : ℝ)) ^ M * Real.exp (-c * n)) := by
  have hr : ‖Real.exp (-c)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (neg_neg_of_pos hc)
  have hs := (summable_pow_mul_geometric_of_norm_lt_one M hr).comp_injective
    (show Function.Injective (fun n : ℕ => n + 1) from fun _ _ h => Nat.add_right_cancel h)
  have ht := hs.mul_left (C * Real.exp c)
  convert ht using 1
  funext n
  simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one, ← Real.exp_nat_mul]
  calc
    C * (1 + (n : ℝ)) ^ M * Real.exp (-c * n) =
        C * ((n : ℝ) + 1) ^ M * Real.exp (c + ((n : ℝ) + 1) * (-c)) := by
      congr 2 <;> ring
    _ = C * Real.exp c * (((n : ℝ) + 1) ^ M * Real.exp (((n : ℝ) + 1) * (-c))) := by
      rw [Real.exp_add]
      ring

variable {P Q Y : Type*} [MetricSpace Y] [CompleteSpace Y]

/-- A common summable increment bound gives actual limits, a common tail
estimate, and uniform convergence of the family of trajectories. -/
theorem exists_uniform_limit_of_summable_steps
    (f : P → ℕ → Y) (d : ℕ → ℝ) (hd : Summable d)
    (hstep : ∀ p n, dist (f p n) (f p (n + 1)) ≤ d n) :
    ∃ b : P → Y,
      (∀ p, Tendsto (f p) atTop (𝓝 (b p))) ∧
      (∀ p n, dist (f p n) (b p) ≤ ∑' k, d (n + k)) ∧
      TendstoUniformly (fun n p => f p n) b atTop := by
  choose b hb using fun p => cauchySeq_tendsto_of_complete
    (cauchySeq_of_dist_le_of_summable d (hstep p) hd)
  have htail (p : P) (n : ℕ) : dist (f p n) (b p) ≤ ∑' k, d (n + k) :=
    dist_le_tsum_of_dist_le_of_tendsto d (hstep p) hd (hb p) n
  refine ⟨b, hb, htail, Metric.tendstoUniformly_iff.mpr ?_⟩
  intro ε hε
  have ht : Tendsto (fun n : ℕ => ∑' k, d (n + k)) atTop (𝓝 0) := by
    simpa only [Nat.add_comm] using tendsto_sum_nat_add d
  filter_upwards [ht.eventually (eventually_lt_nhds hε)] with n hn p
  exact (dist_comm _ _).trans_le (htail p n) |>.trans_lt hn

omit [CompleteSpace Y] in
/-- Asymptotic trajectories represent the same boundary point. -/
theorem boundary_limits_eq_of_asymptotic
    (f g : ℕ → Y) {a b : Y}
    (hf : Tendsto f atTop (𝓝 a)) (hg : Tendsto g atTop (𝓝 b))
    (hfg : Tendsto (fun n => dist (f n) (g n)) atTop (𝓝 0)) : a = b := by
  exact tendsto_nhds_unique (hf.congr_dist hfg) hg

/-- Uniform trajectory convergence and asymptotic equality on quotient
fibers construct the continuous boundary map. The displayed tail estimate
is independent of the quotient point and representative. -/
theorem exists_continuous_quotient_boundary
    [TopologicalSpace P] [TopologicalSpace Q]
    (q : P → Q) (hq : Topology.IsQuotientMap q)
    (f : P → ℕ → Y) (hcont : ∀ n, Continuous (fun p => f p n))
    (d : ℕ → ℝ) (hd : Summable d)
    (hstep : ∀ p n, dist (f p n) (f p (n + 1)) ≤ d n)
    (hfiber : ∀ p p', q p = q p' →
      Tendsto (fun n => dist (f p n) (f p' n)) atTop (𝓝 0)) :
    ∃ b : Q → Y, Continuous b ∧
      TendstoUniformly (fun n p => f p n) (fun p => b (q p)) atTop ∧
      ∀ p n, dist (f p n) (b (q p)) ≤ ∑' k, d (n + k) := by
  obtain ⟨l, hl, htail, huniform⟩ := exists_uniform_limit_of_summable_steps f d hd hstep
  have heq (p p' : P) (h : q p = q p') : l p = l p' :=
    boundary_limits_eq_of_asymptotic (f p) (f p') (hl p) (hl p') (hfiber p p' h)
  choose r hr using hq.surjective
  let b : Q → Y := fun y => l (r y)
  have hb (p : P) : b (q p) = l p := heq _ _ (hr (q p))
  have hbfun : (fun p => b (q p)) = l := funext hb
  refine ⟨b, hq.continuous_iff.mpr ?_, ?_, ?_⟩
  · simpa only [Function.comp_def, hbfun] using
      huniform.continuous (Filter.Eventually.of_forall hcont).frequently
  · simpa only [hbfun] using huniform
  · intro p n
    rw [hb]
    exact htail p n

/-- In the polynomial-exponential case the normalized limit lies in one
fixed compact ball, uniformly over all initial trajectories. -/
theorem exists_compact_boundary_shadow [ProperSpace Y]
    (f : P → ℕ → Y) (y₀ : Y) (hstart : ∀ p, f p 0 = y₀)
    (C : ℝ) (M : ℕ) {c : ℝ} (hc : 0 < c)
    (hstep : ∀ p n, dist (f p n) (f p (n + 1)) ≤
      C * (1 + (n : ℝ)) ^ M * Real.exp (-c * n)) :
    ∃ (K : Set Y) (b : P → Y), IsCompact K ∧
      (∀ p, Tendsto (f p) atTop (𝓝 (b p))) ∧ (∀ p, b p ∈ K) := by
  let d : ℕ → ℝ := fun n => C * (1 + (n : ℝ)) ^ M * Real.exp (-c * n)
  have hd : Summable d := summable_polynomial_exp_decay C M hc
  obtain ⟨b, hb, htail, _⟩ := exists_uniform_limit_of_summable_steps f d hd hstep
  refine ⟨closedBall y₀ (∑' n, d n), b, isCompact_closedBall _ _, hb, ?_⟩
  intro p
  rw [mem_closedBall, dist_comm]
  simpa only [hstart p, zero_add] using htail p 0

end PolycyclicRecognition

end

end OAI
