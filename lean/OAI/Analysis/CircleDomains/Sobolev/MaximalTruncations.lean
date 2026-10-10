import OAI.Analysis.CircleDomains.Sobolev.BoundedMaximalL2
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

/-! Bounded compactly supported increasing approximations to a nonnegative
L² function. Each fixed ball integral converges to the original integral. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

def maximalInputTruncation (f : ℂ → ℝ) (n : ℕ) : ℂ → ℝ :=
  (closedBall 0 (n : ℝ)).indicator (fun x => min (f x) (n : ℝ))

lemma measurable_maximalInputTruncation {f : ℂ → ℝ} (hf : Measurable f) (n : ℕ) :
    Measurable (maximalInputTruncation f n) :=
  (hf.min measurable_const).indicator isClosed_closedBall.measurableSet

lemma maximalInputTruncation_nonneg {f : ℂ → ℝ} (hf0 : ∀ x, 0 ≤ f x) (n : ℕ) (x : ℂ) :
    0 ≤ maximalInputTruncation f n x :=
  indicator_nonneg (fun x _ => le_min (hf0 x) (Nat.cast_nonneg n)) x

lemma maximalInputTruncation_le {f : ℂ → ℝ} (hf0 : ∀ x, 0 ≤ f x) (n : ℕ) (x : ℂ) :
    maximalInputTruncation f n x ≤ f x := by
  by_cases hx : x ∈ closedBall 0 (n : ℝ)
  · simpa only [maximalInputTruncation, indicator_of_mem hx] using min_le_left (f x) (n : ℝ)
  · simpa only [maximalInputTruncation, indicator_of_notMem hx] using hf0 x

lemma maximalInputTruncation_le_bound {f : ℂ → ℝ} (n : ℕ) (x : ℂ) :
    maximalInputTruncation f n x ≤ (n : ℝ) := by
  by_cases hx : x ∈ closedBall 0 (n : ℝ)
  · simpa only [maximalInputTruncation, indicator_of_mem hx] using min_le_right (f x) (n : ℝ)
  · simpa only [maximalInputTruncation, indicator_of_notMem hx] using Nat.cast_nonneg n

lemma maximalInputTruncation_mono {f : ℂ → ℝ} (hf0 : ∀ x, 0 ≤ f x) (x : ℂ) :
    Monotone (fun n => maximalInputTruncation f n x) := by
  intro i j hij
  by_cases hx : x ∈ closedBall 0 (i : ℝ)
  · have hxj : x ∈ closedBall 0 (j : ℝ) := closedBall_subset_closedBall (Nat.cast_le.mpr hij) hx
    simp only [maximalInputTruncation, indicator_of_mem hx, indicator_of_mem hxj]
    exact min_le_min_left _ (Nat.cast_le.mpr hij)
  · simpa only [maximalInputTruncation, indicator_of_notMem hx] using
      maximalInputTruncation_nonneg hf0 j x

lemma maximalInputTruncation_eventually_eq (f : ℂ → ℝ) (x : ℂ) :
    ∀ᶠ n : ℕ in atTop, maximalInputTruncation f n x = f x := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max ‖x‖ (f x))
  filter_upwards [eventually_ge_atTop N] with n hn
  have hb : max ‖x‖ (f x) < (n : ℝ) := hN.trans_le (Nat.cast_le.mpr hn)
  have hx : x ∈ closedBall 0 (n : ℝ) := by
    simpa only [mem_closedBall, dist_zero_right] using (le_max_left ‖x‖ (f x)).trans hb.le
  rw [maximalInputTruncation, indicator_of_mem hx,
    min_eq_left ((le_max_right ‖x‖ (f x)).trans hb.le)]

lemma maximalInputTruncation_memLp {f : ℂ → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hf2 : MemLp f 2 volume) (n : ℕ) :
    MemLp (maximalInputTruncation f n) 2 volume := by
  apply hf2.mono' (measurable_maximalInputTruncation hf n).aestronglyMeasurable
  exact ae_of_all _ (fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (maximalInputTruncation_nonneg hf0 n x)]
    exact maximalInputTruncation_le hf0 n x)

lemma maximalInputTruncation_integrable {f : ℂ → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hf2 : MemLp f 2 volume) (n : ℕ) :
    Integrable (maximalInputTruncation f n) := by
  have hlocal := (hf2.locallyIntegrable (by norm_num)).integrableOn_isCompact
    (isCompact_closedBall (0 : ℂ) (n : ℝ))
  have hmask : Integrable ((closedBall 0 (n : ℝ)).indicator f) :=
    (integrable_indicator_iff isClosed_closedBall.measurableSet).mpr hlocal
  apply hmask.mono_nonneg (measurable_maximalInputTruncation hf n).aestronglyMeasurable
    (ae_of_all _ (maximalInputTruncation_nonneg hf0 n))
  apply ae_of_all
  intro x
  by_cases hx : x ∈ closedBall 0 (n : ℝ)
  · rw [indicator_of_mem hx]
    exact maximalInputTruncation_le hf0 n x
  · simp only [maximalInputTruncation, indicator_of_notMem hx]
    exact le_rfl

lemma maximalInputTruncation_energy_le {f : ℂ → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hf2 : MemLp f 2 volume) (n : ℕ) :
    (∫ x, maximalInputTruncation f n x^2) ≤ ∫ x, f x^2 := by
  apply integral_mono (maximalInputTruncation_memLp hf hf0 hf2 n).integrable_sq hf2.integrable_sq
  intro x
  exact pow_le_pow_left₀ (maximalInputTruncation_nonneg hf0 n x)
    (maximalInputTruncation_le hf0 n x) 2

lemma tendsto_integral_maximalInputTruncation {f : ℂ → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hf2 : MemLp f 2 volume) (x : ℂ) (r : ℝ) :
    Tendsto (fun n => ∫ y in ball x r, maximalInputTruncation f n y)
      atTop (𝓝 (∫ y in ball x r, f y)) := by
  have hlocal := (hf2.locallyIntegrable (by norm_num)).integrableOn_isCompact
    (isCompact_closedBall x r)
  apply tendsto_integral_of_dominated_convergence f
    (fun n => (measurable_maximalInputTruncation hf n).aestronglyMeasurable)
    (hlocal.mono_set ball_subset_closedBall)
  · intro n
    exact ae_of_all _ (fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (maximalInputTruncation_nonneg hf0 n y)]
      exact maximalInputTruncation_le hf0 n y)
  · apply ae_of_all
    intro y
    have he : (fun n => maximalInputTruncation f n y) =ᶠ[atTop] (fun _ => f y) :=
      maximalInputTruncation_eventually_eq f y
    exact tendsto_const_nhds.congr' he.symm

end CircleDomainRigidity

end

end OAI
