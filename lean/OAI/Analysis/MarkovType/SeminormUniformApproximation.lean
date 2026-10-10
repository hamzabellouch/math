import Mathlib.Analysis.Normed.Module.Seminorm.Norm
import Mathlib.Topology.UniformSpace.Dini
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section

open Filter
open scoped NNReal Topology

namespace MarkovSuperreflexivity.SeminormApproximation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem continuous_of_norm_bound (p : Seminorm ℝ E) (C : ℝ≥0)
    (hp : ∀ x, p x ≤ (C : ℝ) * ‖x‖) : Continuous p := by
  have h : LipschitzWith C (fun x => p x) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_eq_norm] using (p.norm_sub_map_le_sub x y).trans (hp (x - y))
  exact h.continuous

theorem exists_relative_approximation [ProperSpace E]
    (p : ℕ → Seminorm ℝ E) (q : Seminorm ℝ E)
    (ha : ∀ x, Antitone fun n => p n x)
    (ht : ∀ x, Tendsto (fun n => p n x) atTop (𝓝 (q x)))
    (C : ℝ≥0) (hC : ∀ n x, p n x ≤ (C : ℝ) * ‖x‖)
    {d : ℝ} (hd : 0 < d) (hcoerce : ∀ x, d * ‖x‖ ≤ q x)
    {η : ℝ} (hη : 0 < η) :
    ∃ n : ℕ, ∀ x, q x ≤ p n x ∧ p n x ≤ (1 + η) * q x := by
  have hqp (x : E) (n : ℕ) : q x ≤ p n x := by
    apply le_of_tendsto (ht x)
    filter_upwards [eventually_ge_atTop n] with k hnk
    exact ha x hnk
  have hqC (x : E) : q x ≤ (C : ℝ) * ‖x‖ :=
    (hqp x 0).trans (hC 0 x)
  have hu : TendstoUniformlyOn (fun n x => p n x) q atTop
      (Metric.closedBall (0 : E) 1) :=
    Antitone.tendstoUniformlyOn_of_forall_tendsto
      (isCompact_closedBall (0 : E) 1)
      (fun n => (continuous_of_norm_bound (p n) C (hC n)).continuousOn)
      (fun x _ => ha x)
      (continuous_of_norm_bound q C hqC).continuousOn
      (fun x _ => ht x)
  obtain ⟨n, hn⟩ :=
    (Metric.tendstoUniformlyOn_iff.mp hu (η * d) (mul_pos hη hd)).exists
  refine ⟨n, fun x => ⟨hqp x n, ?_⟩⟩
  by_cases hx0 : x = 0
  · simp only [hx0, map_zero, mul_zero, le_refl]
  have hx : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  let v : E := ‖x‖⁻¹ • x
  have hv : ‖v‖ = 1 := by
    simp only [v, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hx),
      inv_mul_cancel₀ (ne_of_gt hx)]
  have hxv : ‖x‖ • v = x := by
    simp only [v, smul_smul, mul_inv_cancel₀ (ne_of_gt hx), one_smul]
  have hvball : v ∈ Metric.closedBall (0 : E) 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right, hv] using (le_refl (1 : ℝ))
  have herr : p n v - q v < η * d := by
    have hdist := hn v hvball
    have habs : |p n v - q v| < η * d := by
      simpa only [Real.dist_eq, abs_sub_comm] using hdist
    exact (le_abs_self _).trans_lt habs
  have hdv : d ≤ q v := by simpa only [hv, mul_one] using hcoerce v
  have hvbound : p n v ≤ (1 + η) * q v := by nlinarith
  have hscale (s : Seminorm ℝ E) : s x = ‖x‖ * s v := by
    calc
      s x = s (‖x‖ • v) := congrArg s hxv.symm
      _ = ‖x‖ * s v := by
        rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x)]
  rw [hscale (p n), hscale q]
  calc
    ‖x‖ * p n v ≤ ‖x‖ * ((1 + η) * q v) :=
      mul_le_mul_of_nonneg_left hvbound hx.le
    _ = (1 + η) * (‖x‖ * q v) := by ring

end MarkovSuperreflexivity.SeminormApproximation

end

end OAI
