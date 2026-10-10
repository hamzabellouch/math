import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace OAI

open Filter Finset
open scoped Topology

namespace Zeta5.Workers.W14

noncomputable def primeIntervalSum (x y : ℝ) : ℝ :=
  ∑ p ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊ with p.Prime, Real.log (p : ℝ)

theorem mem_primeInterval_iff {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (p : ℕ) :
    p ∈ (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter Nat.Prime ↔
      x < (p : ℝ) ∧ (p : ℝ) ≤ y ∧ p.Prime := by
  simp only [Finset.mem_filter, Finset.mem_Ioc,
    Nat.floor_lt hx, Nat.le_floor_iff (hx.trans hxy), and_assoc]

theorem primeIntervalSum_eq_theta_sub {x y : ℝ} (hxy : x ≤ y) :
    primeIntervalSum x y = Chebyshev.theta y - Chebyshev.theta x := by
  unfold primeIntervalSum Chebyshev.theta
  simp only [Finset.sum_filter]
  have h := Finset.sum_Ioc_consecutive
    (fun p : ℕ => if p.Prime then Real.log (p : ℝ) else 0)
    (Nat.zero_le ⌊x⌋₊) (Nat.floor_le_floor hxy)
  exact eq_sub_iff_add_eq.mpr (by simpa [add_comm] using h)

theorem theta_scaled_tendsto
    (hPNT : Tendsto (fun R : ℝ => Chebyshev.theta R / R) atTop (𝓝 1))
    {c : ℝ} (hc : 0 < c) :
    Tendsto (fun R : ℝ => Chebyshev.theta (c * R) / R) atTop (𝓝 c) := by
  have hscale : Tendsto (fun R : ℝ => c * R) atTop atTop :=
    tendsto_id.const_mul_atTop hc
  have h := (hPNT.comp hscale).const_mul c
  simp only [mul_one] at h
  apply h.congr
  intro R
  change c * (Chebyshev.theta (c * R) / (c * R)) = Chebyshev.theta (c * R) / R
  rw [← mul_div_assoc, mul_div_mul_left _ _ (ne_of_gt hc)]

theorem primeIntervalSum_scaled_tendsto
    (hPNT : Tendsto (fun R : ℝ => Chebyshev.theta R / R) atTop (𝓝 1))
    {α β : ℝ} (hα : 0 < α) (hαβ : α < β) :
    Tendsto (fun R : ℝ => primeIntervalSum (α * R) (β * R) / R)
      atTop (𝓝 (β - α)) := by
  have h := (theta_scaled_tendsto hPNT (hα.trans hαβ)).sub
    (theta_scaled_tendsto hPNT hα)
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
  rw [primeIntervalSum_eq_theta_sub (mul_le_mul_of_nonneg_right hαβ.le hR), sub_div]

noncomputable def weightedPrimeIntervalSum (F : ℝ → ℝ) (α β R : ℝ) : ℝ :=
  (∑ p ∈ Finset.Ioc ⌊α * R⌋₊ ⌊β * R⌋₊ with p.Prime,
    F ((p : ℝ) / R) * Real.log (p : ℝ)) / R

theorem weightedPrimeIntervalSum_const (c α β R : ℝ) :
    weightedPrimeIntervalSum (fun _ => c) α β R =
      c * (primeIntervalSum (α * R) (β * R) / R) := by
  simp only [weightedPrimeIntervalSum, primeIntervalSum, ← Finset.mul_sum,
    mul_div_assoc]

theorem weightedPrimeIntervalSum_const_tendsto
    (hPNT : Tendsto (fun R : ℝ => Chebyshev.theta R / R) atTop (𝓝 1))
    {α β : ℝ} (hα : 0 < α) (hαβ : α < β) (c : ℝ) :
    Tendsto (weightedPrimeIntervalSum (fun _ => c) α β) atTop
      (𝓝 (∫ _ in α..β, c)) := by
  have h := (primeIntervalSum_scaled_tendsto hPNT hα hαβ).const_mul c
  have hfun : weightedPrimeIntervalSum (fun _ => c) α β =
      (fun R : ℝ => c * (primeIntervalSum (α * R) (β * R) / R)) := by
    funext R
    exact weightedPrimeIntervalSum_const c α β R
  rw [hfun]
  simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using h

noncomputable def finiteStepPrimeSum {ι : Type*} (s : Finset ι)
    (a b weight : ι → ℝ) (R : ℝ) : ℝ :=
  ∑ i ∈ s, weight i * (primeIntervalSum (a i * R) (b i * R) / R)

theorem finiteStepPrimeSum_tendsto {ι : Type*} (s : Finset ι)
    (a b weight : ι → ℝ)
    (hPNT : Tendsto (fun R : ℝ => Chebyshev.theta R / R) atTop (𝓝 1))
    (ha : ∀ i ∈ s, 0 < a i) (hab : ∀ i ∈ s, a i < b i) :
    Tendsto (finiteStepPrimeSum s a b weight) atTop
      (𝓝 (∑ i ∈ s, weight i * (b i - a i))) := by
  apply tendsto_finsetSum s
  intro i hi
  exact (primeIntervalSum_scaled_tendsto hPNT (ha i hi) (hab i hi)).const_mul (weight i)

end Zeta5.Workers.W14

end OAI
