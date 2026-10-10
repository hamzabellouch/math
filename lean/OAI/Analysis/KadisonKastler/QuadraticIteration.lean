import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Tactic.Linarith

namespace OAI

/-! # Convergence of the quadratic boundary correction

The constants are the ones used by the cocycle averaging step: defect
`e` improves to `16e²`, at displacement at most `e + 4e²`.
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

/-- Iterating the quadratic improvement gives an exact solution within
`2e`, where `e ≤ 1/64` is the original defect. -/
theorem exists_zero_of_quadratic_improvement
    {X : Type*} [MetricSpace X] [CompleteSpace X]
    (d : X → ℝ) (hd : Continuous d) (hd0 : ∀ x, 0 ≤ d x)
    (hstep : ∀ x, d x ≤ 1 / 64 → ∃ y,
      d y ≤ 16 * (d x) ^ 2 ∧ dist x y ≤ d x + 4 * (d x) ^ 2)
    (x₀ : X) (hx₀ : d x₀ ≤ 1 / 64) :
    ∃ y, d y = 0 ∧ dist x₀ y ≤ 2 * d x₀ := by
  let S := {x : X // d x ≤ 1 / 64}
  have hquarter (x : S) : 16 * (d x.val) ^ 2 ≤ d x.val / 4 := by
    have hp := hd0 x.val
    have hb := x.property
    nlinarith
  let next : S → S := fun x =>
    ⟨Classical.choose (hstep x.val x.property),
      ((Classical.choose_spec (hstep x.val x.property)).1.trans
        (hquarter x)).trans (by have hx := x.property; linarith)⟩
  have hnext (x : S) : d (next x).val ≤ d x.val / 4 ∧
      dist x.val (next x).val ≤ d x.val + 4 * (d x.val) ^ 2 := by
    exact ⟨(Classical.choose_spec (hstep x.val x.property)).1.trans (hquarter x),
      (Classical.choose_spec (hstep x.val x.property)).2⟩
  let s : ℕ → S := fun n => (next^[n]) ⟨x₀, hx₀⟩
  have hs0 : (s 0).val = x₀ := rfl
  have hsnext (n : ℕ) : s (n + 1) = next (s n) := by
    exact Function.iterate_succ_apply' next n ⟨x₀, hx₀⟩
  have hdecay (n : ℕ) : d (s n).val ≤ d x₀ * (1 / 4 : ℝ) ^ n := by
    induction n with
    | zero => simp only [hs0, pow_zero, mul_one, le_refl]
    | succ n ih =>
      rw [hsnext]
      calc
        _ ≤ d (s n).val / 4 := (hnext (s n)).1
        _ ≤ (d x₀ * (1 / 4 : ℝ) ^ n) / 4 := div_le_div_of_nonneg_right ih (by norm_num)
        _ = _ := by rw [pow_succ]; ring
  have hdist (n : ℕ) : dist (s n).val (s (n + 1)).val ≤
      (17 / 16 * d x₀) * (1 / 4 : ℝ) ^ n := by
    rw [hsnext]
    calc
      _ ≤ d (s n).val + 4 * (d (s n).val) ^ 2 := (hnext (s n)).2
      _ ≤ 17 / 16 * d (s n).val := by
        have hp := hd0 (s n).val
        have hb := (s n).property
        nlinarith
      _ ≤ 17 / 16 * (d x₀ * (1 / 4 : ℝ) ^ n) :=
        mul_le_mul_of_nonneg_left (hdecay n) (by norm_num)
      _ = _ := by ring
  have hc : CauchySeq (fun n => (s n).val) :=
    cauchySeq_of_le_geometric (1 / 4) (17 / 16 * d x₀) (by norm_num) hdist
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hc
  have hdz : Tendsto (fun n => d (s n).val) atTop (𝓝 0) := by
    have hgeom : Tendsto (fun n : ℕ => d x₀ * (1 / 4 : ℝ) ^ n) atTop (𝓝 0) := by
      simpa only [mul_zero] using
        (tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one
          (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num : (1 / 4 : ℝ) < 1)))
    exact squeeze_zero (fun n => hd0 (s n).val) hdecay hgeom
  have hdy : d y = 0 := tendsto_nhds_unique (hd.continuousAt.tendsto.comp hy) hdz
  refine ⟨y, hdy, ?_⟩
  have hb := dist_le_of_le_geometric_of_tendsto₀ (1 / 4)
    (17 / 16 * d x₀) (by norm_num) hdist hy
  rw [hs0] at hb
  norm_num at hb
  have hp := hd0 x₀
  linarith

end

end KadisonKastler

end OAI
