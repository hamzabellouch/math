import OAI.Probability.FirstPassage.GridProbability
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace OAI

namespace PlanarFPP
open Filter Finset Set
open scoped Topology

lemma summable_grid_gaussian (a : ℝ) (ha : 0 < a) :
    Summable (fun j : ℕ => (2 : ℝ)^(5*j)*Real.exp (-a*(j : ℝ)^2)) := by
  obtain ⟨N,hN⟩ := exists_nat_gt ((5*Real.log 2+1)/a)
  apply (summable_nat_add_iff N).mp
  have hs : Summable (fun n : ℕ => Real.exp (-1)^n) :=
    summable_geometric_of_norm_lt_one (by rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]; exact Real.exp_lt_one_iff.mpr (by norm_num))
  apply hs.of_nonneg_of_le (fun _ => by positivity)
  intro n
  have hNa : 5*Real.log 2+1 < (N : ℝ)*a := (div_lt_iff₀ ha).mp hN
  have hja : 5*Real.log 2+1 ≤ a*((n+N : ℕ) : ℝ) := by push_cast; nlinarith
  have hmul := mul_le_mul_of_nonneg_right hja (show 0 ≤ ((n+N : ℕ) : ℝ) by positivity)
  rw [show (2 : ℝ)^(5*(n+N))=Real.exp ((5*(n+N : ℕ) : ℕ)*Real.log 2) by
    rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0 : ℝ)<2)],← Real.exp_add,← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  push_cast at hmul ⊢
  nlinarith

noncomputable def gridFailureSeries (q : ℝ) (j : ℕ) : ℝ :=
  (2 : ℝ)^(5*j)*(Real.exp (-q*(j : ℝ)^2)+2*Real.exp (-gridVerticalExponent*(j : ℝ)^2))

lemma gridFailureSeries_nonneg (q : ℝ) (j : ℕ) : 0 ≤ gridFailureSeries q j := by
  unfold gridFailureSeries
  positivity

lemma summable_gridFailureSeries (q : ℝ) (hq : 0 < q) : Summable (gridFailureSeries q) := by
  have h := (summable_grid_gaussian q hq).add
    ((summable_grid_gaussian gridVerticalExponent gridVerticalExponent_pos).mul_left 2)
  apply h.congr
  intro j
  unfold gridFailureSeries
  ring

noncomputable def gridFailureTail (C q : ℝ) (J : ℕ) : ℝ :=
  C*(∑' n : ℕ,gridFailureSeries q (n+J))

lemma gridFailureTail_tendsto (C q : ℝ) (_hq : 0 < q) :
    Tendsto (gridFailureTail C q) atTop (𝓝 0) := by
  have h := tendsto_sum_nat_add (gridFailureSeries q)
  change Tendsto (fun J : ℕ => C*(∑' n : ℕ,gridFailureSeries q (n+J))) atTop (𝓝 0)
  simpa only [mul_zero] using h.const_mul C

lemma gridFailureTail_nonneg (C q : ℝ) (hC : 0 ≤ C) (J : ℕ) :
    0 ≤ gridFailureTail C q J :=
  mul_nonneg hC (tsum_nonneg (fun _ => gridFailureSeries_nonneg q _))

lemma grid_level_failure_le_series (q : ℝ) (_hq : 0 ≤ q) (hq1 : q ≤ 1)
    (j : ℕ) (w : ℝ) (hw : 1 ≤ w) :
    (2 : ℝ)^(5*j)*((1-q)^(j^2)+2*Real.exp (-gridVerticalExponent*(j : ℝ)^2*w)) ≤
      gridFailureSeries q j := by
  have hb : 1-q ≤ Real.exp (-q) := by have hh := Real.add_one_le_exp (-q); linarith
  have hp := pow_le_pow_left₀ (show 0 ≤ 1-q by linarith) hb (j^2)
  have hp' : (1-q)^(j^2) ≤ Real.exp (-q*(j : ℝ)^2) := by
    rw [← Real.exp_nat_mul] at hp
    simpa only [Nat.cast_pow,mul_comm] using hp
  have he : Real.exp (-gridVerticalExponent*(j : ℝ)^2*w) ≤
      Real.exp (-gridVerticalExponent*(j : ℝ)^2) := by
    apply Real.exp_le_exp.mpr
    have ht := mul_le_mul_of_nonneg_left hw
      (mul_nonneg gridVerticalExponent_pos.le (sq_nonneg (j : ℝ)))
    nlinarith
  unfold gridFailureSeries
  gcongr

end PlanarFPP

end OAI
