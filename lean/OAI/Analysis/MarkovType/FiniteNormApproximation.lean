import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section

open Filter
open scoped Topology

namespace MarkovSuperreflexivity

universe u v

variable {E : Type u} {X : Type v}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem eventually_norm_sub_le_of_pointwise
    (U : Filter ℕ) [U.NeBot] (T : ℕ → E →ₗ[ℝ] X)
    (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ n x, ‖T n x‖ ≤ K * ‖x‖)
    (hlim : ∀ x, Tendsto (fun n => ‖T n x‖) U (𝓝 ‖x‖))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in U, ∀ x, |‖T n x‖ - ‖x‖| ≤ ε * ‖x‖ := by
  have hK1 : 0 < K + 1 := by linarith
  let δ : ℝ := (K + 1)⁻¹ * (ε / 2)
  have hδ : 0 < δ := mul_pos (inv_pos.mpr hK1) (half_pos hε)
  have hδeq : (K + 1) * δ = ε / 2 := by
    dsimp only [δ]
    rw [← mul_assoc, mul_inv_cancel₀ hK1.ne', one_mul]
  obtain ⟨t, _htsub, htfin, hcover⟩ :=
    (isCompact_closedBall (0 : E) 1).finite_cover_balls hδ
  have hnet : ∀ᶠ n in U, ∀ y ∈ t, |‖T n y‖ - ‖y‖| < ε / 2 := by
    apply htfin.eventually_all.2
    intro y _hy
    simpa only [Real.dist_eq] using
      (Metric.tendsto_nhds.1 (hlim y) (ε / 2) (half_pos hε))
  have hball : ∀ᶠ n in U, ∀ v ∈ Metric.closedBall (0 : E) 1,
      |‖T n v‖ - ‖v‖| ≤ ε := by
    refine hnet.mono fun n hn v hv => ?_
    obtain ⟨y, hyt, hvy⟩ := Set.mem_iUnion₂.mp (hcover hv)
    have hdist : ‖v - y‖ ≤ δ := by
      have hlt : ‖v - y‖ < δ := by
        simpa only [dist_eq_norm] using (Metric.mem_ball.mp hvy)
      exact hlt.le
    have hTdist : |‖T n v‖ - ‖T n y‖| ≤ K * ‖v - y‖ := by
      calc
        |‖T n v‖ - ‖T n y‖| ≤ ‖T n v - T n y‖ := abs_norm_sub_norm_le _ _
        _ = ‖T n (v - y)‖ := by rw [map_sub]
        _ ≤ K * ‖v - y‖ := hbound n (v - y)
    have hnormdist : |‖y‖ - ‖v‖| ≤ ‖v - y‖ := by
      calc
        |‖y‖ - ‖v‖| ≤ ‖y - v‖ := abs_norm_sub_norm_le _ _
        _ = ‖v - y‖ := norm_sub_rev _ _
    calc
      |‖T n v‖ - ‖v‖| =
          |(‖T n v‖ - ‖T n y‖) + (‖T n y‖ - ‖y‖) + (‖y‖ - ‖v‖)| := by
        congr 1
        ring
      _ ≤ |(‖T n v‖ - ‖T n y‖) + (‖T n y‖ - ‖y‖)| + |‖y‖ - ‖v‖| :=
        abs_add_le _ _
      _ ≤ (|‖T n v‖ - ‖T n y‖| + |‖T n y‖ - ‖y‖|) + |‖y‖ - ‖v‖| :=
        add_le_add_left (abs_add_le _ _) _
      _ ≤ (K * ‖v - y‖ + ε / 2) + ‖v - y‖ :=
        add_le_add (add_le_add hTdist (hn y hyt).le) hnormdist
      _ ≤ (K * δ + ε / 2) + δ :=
        add_le_add (add_le_add_left (mul_le_mul_of_nonneg_left hdist hK) _) hdist
      _ = ε := by nlinarith [hδeq]
  refine hball.mono fun n hn x => ?_
  by_cases hx0 : x = 0
  · simp [hx0]
  have hx : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  let v : E := ‖x‖⁻¹ • x
  have hv : ‖v‖ = 1 := by
    simp only [v, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hx),
      inv_mul_cancel₀ hx.ne']
  have hxv : ‖x‖ • v = x := by
    simp only [v, smul_smul, mul_inv_cancel₀ hx.ne', one_smul]
  have hvball : v ∈ Metric.closedBall (0 : E) 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right, hv] using (le_refl (1 : ℝ))
  have hvbound : |‖T n v‖ - 1| ≤ ε := by
    simpa only [hv] using hn v hvball
  have hscale : ‖T n x‖ = ‖x‖ * ‖T n v‖ := by
    calc
      ‖T n x‖ = ‖T n (‖x‖ • v)‖ := congrArg (fun z => ‖T n z‖) hxv.symm
      _ = ‖x‖ * ‖T n v‖ := by
        rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x)]
  calc
    |‖T n x‖ - ‖x‖| = |‖x‖ * (‖T n v‖ - 1)| := by
      rw [hscale]
      congr 1
      ring
    _ = ‖x‖ * |‖T n v‖ - 1| := by
      rw [abs_mul, abs_of_nonneg (norm_nonneg x)]
    _ ≤ ‖x‖ * ε := mul_le_mul_of_nonneg_left hvbound hx.le
    _ = ε * ‖x‖ := mul_comm _ _

theorem exists_scaled_norm_bounds_of_pointwise
    (U : Filter ℕ) [U.NeBot] (T : ℕ → E →ₗ[ℝ] X)
    (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ n x, ‖T n x‖ ≤ K * ‖x‖)
    (hlim : ∀ x, Tendsto (fun n => ‖T n x‖) U (𝓝 ‖x‖))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ S : E →ₗ[ℝ] X, ∀ x,
      ‖x‖ ≤ ‖S x‖ ∧ ‖S x‖ ≤ ((1 + ε) / (1 - ε)) * ‖x‖ := by
  obtain ⟨n, hn⟩ :=
    (eventually_norm_sub_le_of_pointwise U T K hK hbound hlim hε).exists
  have hden : 0 < 1 - ε := sub_pos.mpr hε1
  let S : E →ₗ[ℝ] X := (1 - ε)⁻¹ • T n
  have hS (x : E) : ‖S x‖ = ‖T n x‖ / (1 - ε) := by
    change ‖(1 - ε)⁻¹ • T n x‖ = _
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hden), div_eq_mul_inv]
    exact mul_comm _ _
  refine ⟨S, fun x => ?_⟩
  have hlo := (abs_le.mp (hn x)).1
  have hhi := (abs_le.mp (hn x)).2
  rw [hS x]
  constructor
  · apply (le_div_iff₀ hden).2
    nlinarith
  · calc
      ‖T n x‖ / (1 - ε) ≤ ((1 + ε) * ‖x‖) / (1 - ε) := by
        apply (div_le_div_iff_of_pos_right hden).2
        nlinarith
      _ = ((1 + ε) / (1 - ε)) * ‖x‖ := by ring

theorem exists_near_isometric_map_of_pointwise
    (U : Filter ℕ) [U.NeBot] (T : ℕ → E →ₗ[ℝ] X)
    (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ n x, ‖T n x‖ ≤ K * ‖x‖)
    (hlim : ∀ x, Tendsto (fun n => ‖T n x‖) U (𝓝 ‖x‖))
    {η : ℝ} (hη : 0 < η) :
    ∃ S : E →ₗ[ℝ] X, ∀ x, ‖x‖ ≤ ‖S x‖ ∧ ‖S x‖ ≤ (1 + η) * ‖x‖ := by
  let ε : ℝ := min (η / 4) (1 / 2)
  have hε : 0 < ε := lt_min (by linarith) (by linarith)
  have hεη : ε ≤ η / 4 := min_le_left _ _
  have hεhalf : ε ≤ 1 / 2 := min_le_right _ _
  have hε1 : ε < 1 := lt_of_le_of_lt hεhalf (by linarith)
  obtain ⟨S, hS⟩ :=
    exists_scaled_norm_bounds_of_pointwise U T K hK hbound hlim hε hε1
  have hratio : (1 + ε) / (1 - ε) ≤ 1 + η := by
    apply (div_le_iff₀ (sub_pos.mpr hε1)).2
    have hprod := mul_le_mul_of_nonneg_left hεhalf hη.le
    nlinarith
  exact ⟨S, fun x => ⟨(hS x).1,
    (hS x).2.trans (mul_le_mul_of_nonneg_right hratio (norm_nonneg x))⟩⟩

end MarkovSuperreflexivity

end

end OAI
