import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

namespace OAI

/-! # Strong convergence from vanishing fixed cutoffs and a uniform reciprocal remainder -/

open Filter Topology

namespace DefocusingNLS

theorem tendsto_zero_of_uniform_cutoff {E : Type*} [SeminormedAddCommGroup E]
    (f : ℕ → E) (g : (R : ℝ) → 1 ≤ R → ℕ → E) (C : ℝ) (hC : 0 ≤ C)
    (hg : ∀ (R : ℝ) (hR : 1 ≤ R), Tendsto (g R hR) atTop (𝓝 0))
    (hrem : ∀ (R : ℝ) (hR : 1 ≤ R), ∀ n, ‖f n - g R hR n‖ ≤ C / R) :
    Tendsto f atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  let R : ℝ := 1 + 2 * C / ε
  have hR : 1 ≤ R := by
    dsimp [R]
    linarith [div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hC) hε.le]
  have hRp : 0 < R := by linarith
  have hmul : ε * R = ε + 2 * C := by
    dsimp [R]
    field_simp
  have hsmall : C / R < ε / 2 := by
    rw [div_lt_iff₀ hRp]
    nlinarith
  obtain ⟨n₀, hn₀⟩ := Metric.tendsto_atTop.mp (hg R hR) (ε / 2) (by positivity)
  refine ⟨n₀, ?_⟩
  intro n hn
  have hl := hn₀ n hn
  rw [dist_zero_right] at hl ⊢
  have hb := norm_add_le (f n - g R hR n) (g R hR n)
  rw [sub_add_cancel] at hb
  calc
    ‖f n‖ ≤ ‖f n - g R hR n‖ + ‖g R hR n‖ := hb
    _ ≤ C / R + ‖g R hR n‖ := add_le_add (hrem R hR n) le_rfl
    _ < ε := by linarith

end DefocusingNLS

end OAI
