import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Order.Interval.Set.Union
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.UniformSpace.HeineCantor
import OAI.NumberTheory.ZetaFive.Arithmetic.LargePrimeWeighted

namespace OAI

open Filter Finset
open scoped Topology

namespace Zeta5.Workers.W14

theorem continuous_darboux {F : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hF : ContinuousOn F (Set.Icc a b)) :
    ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (p l u : ℕ → ℝ),
      Monotone p ∧ p 0 = a ∧ p n = b ∧
      (∀ i < n, p i < p (i + 1)) ∧
      (∀ i < n, ∀ x ∈ Set.Ioc (p i) (p (i + 1)), l i ≤ F x ∧ F x ≤ u i) ∧
      (∫ x in a..b, F x) - ε < ∑ i ∈ Finset.range n, l i * (p (i + 1) - p i) ∧
      (∑ i ∈ Finset.range n, u i * (p (i + 1) - p i)) < (∫ x in a..b, F x) + ε := by
  intro ε hε
  let η := ε / (4 * (b - a))
  have hη : 0 < η := div_pos hε (mul_pos (by norm_num) (sub_pos.mpr hab))
  have hu := isCompact_Icc.uniformContinuousOn_of_continuous hF
  obtain ⟨δ, hδ, huv⟩ := Metric.uniformContinuousOn_iff.mp hu η hη
  obtain ⟨n, hn⟩ := exists_nat_gt (max 1 ((b - a) / δ))
  have hn0 : 0 < n := by
    have h : (0 : ℝ) < n := lt_trans (by norm_num) ((le_max_left _ _).trans_lt hn)
    exact_mod_cast h
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hmesh : (b - a) / n < δ := by
    apply (div_lt_iff₀ hnR).mpr
    have h := (div_lt_iff₀ hδ).mp ((le_max_right (1 : ℝ) ((b - a) / δ)).trans_lt hn)
    nlinarith
  let p := affineGrid a b n
  let l := fun i => F (p i) - η
  let u := fun i => F (p i) + η
  have hp : StrictMono p := grid_strict hab hn0
  have hp0 : p 0 = a := grid_zero a b n
  have hpn : p n = b := grid_end a b hn0
  have hsub : ∀ i < n, Set.Icc (p i) (p (i + 1)) ⊆ Set.Icc a b := by
    intro i hi x hx
    have hlo := hp.monotone (Nat.zero_le i)
    have hhi := hp.monotone (show i + 1 ≤ n by omega)
    rw [hp0] at hlo
    rw [hpn] at hhi
    exact ⟨hlo.trans hx.1, hx.2.trans hhi⟩
  have hcell : ∀ i < n, ∀ x ∈ Set.Icc (p i) (p (i + 1)), l i ≤ F x ∧ F x ≤ u i := by
    intro i hi x hx
    have hpi : p i ∈ Set.Icc a b := hsub i hi ⟨le_rfl, (hp (Nat.lt_succ_self i)).le⟩
    have hd : dist x (p i) < δ := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hx.1)]
      have hw : p (i + 1) - p i = (b - a) / n := grid_width a b n i
      linarith [hx.2]
    have h := huv x (hsub i hi hx) (p i) hpi hd
    rw [Real.dist_eq] at h
    have hh := abs_lt.mp h
    dsimp [l, u]
    constructor <;> linarith
  have hint : ∀ i < n, IntervalIntegrable F MeasureTheory.volume (p i) (p (i + 1)) := by
    intro i hi
    exact ContinuousOn.intervalIntegrable_of_Icc (hp (Nat.lt_succ_self i)).le
      (hF.mono (hsub i hi))
  have hsumInt : (∑ i ∈ Finset.range n, ∫ x in p i..p (i + 1), F x) = ∫ x in a..b, F x := by
    simpa only [hp0, hpn] using intervalIntegral.sum_integral_adjacent_intervals hint
  have hlo : (∑ i ∈ Finset.range n, l i * (p (i + 1) - p i)) ≤ ∫ x in a..b, F x := by
    rw [← hsumInt]
    apply Finset.sum_le_sum
    intro i hi
    have h := intervalIntegral.integral_mono_on (hp (Nat.lt_succ_self i)).le
      (continuous_const.intervalIntegrable (p i) (p (i + 1)) : IntervalIntegrable (fun _ : ℝ => l i)
        MeasureTheory.volume (p i) (p (i + 1))) (hint i (Finset.mem_range.mp hi))
      (fun x hx => (hcell i (Finset.mem_range.mp hi) x hx).1)
    simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using h
  have hhi : (∫ x in a..b, F x) ≤ ∑ i ∈ Finset.range n, u i * (p (i + 1) - p i) := by
    rw [← hsumInt]
    apply Finset.sum_le_sum
    intro i hi
    have h := intervalIntegral.integral_mono_on (hp (Nat.lt_succ_self i)).le
      (hint i (Finset.mem_range.mp hi))
      (continuous_const.intervalIntegrable (p i) (p (i + 1)) : IntervalIntegrable (fun _ : ℝ => u i)
        MeasureTheory.volume (p i) (p (i + 1)))
      (fun x hx => (hcell i (Finset.mem_range.mp hi) x hx).2)
    simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using h
  have hgap : (∑ i ∈ Finset.range n, u i * (p (i + 1) - p i)) -
      (∑ i ∈ Finset.range n, l i * (p (i + 1) - p i)) = 2 * η * (b - a) := by
    rw [← Finset.sum_sub_distrib]
    have heq : ∀ i : ℕ, u i * (p (i + 1) - p i) - l i * (p (i + 1) - p i) =
        (2 * η) * (p (i + 1) - p i) := by intro i; dsimp [u, l]; ring
    simp_rw [heq]
    rw [← Finset.mul_sum, Finset.sum_range_sub, hp0, hpn]
  have hsmall : 2 * η * (b - a) < ε := by
    dsimp [η]
    have hbane : b - a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
    have heq : 2 * (ε / (4 * (b - a))) * (b - a) = ε / 2 := by field_simp [hbane]; ring
    rw [heq]
    linarith
  refine ⟨n, p, l, u, hp.monotone, hp0, hpn, fun i _ => hp (Nat.lt_succ_self i),
    fun i hi x hx => hcell i hi x ⟨hx.1.le, hx.2⟩, ?_, ?_⟩ <;> linarith

theorem continuous_weightedPrime_tendsto {F : ℝ → ℝ} {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hF : ContinuousOn F (Set.Icc a b))
    (hPNT : Tendsto (fun R : ℝ => Chebyshev.theta R / R) atTop (𝓝 1)) :
    Tendsto (weightedPrimeIntervalSum F a b) atTop (𝓝 (∫ x in a..b, F x)) :=
  weightedPrimeIntervalSum_tendsto_of_darboux ha hab hPNT (continuous_darboux hab hF)

theorem continuous_extension_weightedPrime_tendsto {F G : ℝ → ℝ} {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hG : ContinuousOn G (Set.Icc a b))
    (hFG : ∀ x ∈ Set.Ioc a b, F x = G x)
    (hPNT : Tendsto (fun R : ℝ => Chebyshev.theta R / R) atTop (𝓝 1)) :
    Tendsto (weightedPrimeIntervalSum F a b) atTop (𝓝 (∫ x in a..b, F x)) := by
  have hInt : (∫ x in a..b, F x) = ∫ x in a..b, G x := by
    apply intervalIntegral.integral_congr_ae'
    · exact Eventually.of_forall hFG
    · exact Eventually.of_forall (fun x hx => False.elim
        ((not_lt_of_ge (hx.2.trans hab.le)) hx.1))
  have h := continuous_weightedPrime_tendsto ha hab hG hPNT
  rw [← hInt] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  apply le_antisymm
  · exact weightedPrimeIntervalSum_mono ha.le hab.le hR (fun x hx => (hFG x hx).symm.le)
  · exact weightedPrimeIntervalSum_mono ha.le hab.le hR (fun x hx => (hFG x hx).le)

end Zeta5.Workers.W14

end OAI
