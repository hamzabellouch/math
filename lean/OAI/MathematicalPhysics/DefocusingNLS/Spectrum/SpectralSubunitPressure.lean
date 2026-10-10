import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.UniformSpace.UniformConvergence

namespace OAI

/-! The pressure divided by its small scale vanishes uniformly where the limiting amplitude is subunit. -/

open Set Filter Topology
namespace DefocusingNLS

theorem spectralSubunit_scaled_power_uniform {s : Set ℝ} (H : ℕ → ℝ → ℝ) (H₀ : ℝ → ℝ)
    (hH : TendstoUniformlyOn H H₀ atTop s) (ρ : ℝ) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hbound : ∀ r ∈ s, ‖H₀ r‖ ≤ ρ) (p : ℕ → ℕ) (hp : Tendsto p atTop atTop) :
    TendstoUniformlyOn (fun n r => (p n : ℝ)*(H n r)^(p n)) (fun _ => 0) atTop s := by
  let q := (ρ+1)/2
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q < 1 := by dsimp [q]; linarith
  have hgap : 0 < q-ρ := by dsimp [q]; linarith
  have hclose : ∀ᶠ n in atTop, ∀ r ∈ s, ‖H n r‖ ≤ q := by
    filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hH) (q-ρ) hgap] with n hn r hr
    have hd : ‖H n r-H₀ r‖ < q-ρ := by
      simpa only [dist_eq_norm,norm_sub_rev] using hn r hr
    exact (norm_le_norm_sub_add (H n r) (H₀ r)).trans (by linarith [hbound r hr])
  have hdecay : Tendsto (fun n => (p n : ℝ)*q^(p n)) atTop (𝓝 0) :=
    (tendsto_self_mul_const_pow_of_lt_one hq0 hq1).comp hp
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hclose,hdecay.eventually (Iio_mem_nhds hε)] with n hn hb r hr
  rw [dist_zero_left,norm_mul,norm_pow,Real.norm_natCast]
  exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hn r hr) (p n))
    (Nat.cast_nonneg (p n))).trans_lt hb

end DefocusingNLS

end OAI
