import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Tactic

namespace OAI

open Filter Topology
open scoped BigOperators

namespace Invariant233

theorem norm_geometric_sum_le (r : ℂ) (hr : r ≠ 1) (hrnorm : ‖r‖ = 1)
    (n : ℕ) :
    ‖∑ k ∈ Finset.range n, r ^ k‖ ≤ 2 / ‖r - 1‖ := by
  rw [geom_sum_eq hr, norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  calc
    ‖r ^ n - 1‖ ≤ ‖r ^ n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by norm_num [norm_pow, hrnorm]

theorem norm_geometric_average_le (r z : ℂ) (hr : r ≠ 1)
    (hrnorm : ‖r‖ = 1) (n : ℕ) :
    ‖(∑ k ∈ Finset.range n, z * r ^ k) / (n : ℂ)‖ ≤
      (‖z‖ * (2 / ‖r - 1‖)) / (n : ℝ) := by
  rw [← Finset.mul_sum, norm_div, norm_mul, norm_natCast]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  exact mul_le_mul_of_nonneg_left (norm_geometric_sum_le r hr hrnorm n) (norm_nonneg z)

theorem norm_geometric_average_le_of_norm_le_one (r z : ℂ) (hr : r ≠ 1)
    (hrnorm : ‖r‖ = 1) (hz : ‖z‖ ≤ 1) (n : ℕ) :
    ‖(∑ k ∈ Finset.range n, z * r ^ k) / (n : ℂ)‖ ≤
      (2 / ‖r - 1‖) / (n : ℝ) := by
  apply (norm_geometric_average_le r z hr hrnorm n).trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  simpa using mul_le_mul_of_nonneg_right hz
    (show 0 ≤ 2 / ‖r - 1‖ by positivity)

theorem tendstoUniformlyOn_geometric_average (r : ℂ) (hr : r ≠ 1)
    (hrnorm : ‖r‖ = 1) :
    TendstoUniformlyOn
      (fun n : ℕ => fun z : ℂ => (∑ k ∈ Finset.range n, z * r ^ k) / (n : ℂ))
      (fun _ => 0) atTop {z : ℂ | ‖z‖ ≤ 1} := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hlim : Tendsto (fun n : ℕ => (2 / ‖r - 1‖) / (n : ℝ))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  filter_upwards [(tendsto_order.mp hlim).2 ε hε] with n hn
  intro z hz
  simpa only [dist_zero_left] using
    (norm_geometric_average_le_of_norm_le_one r z hr hrnorm hz n).trans_lt hn

theorem fourier_rotation_orbit (m : ℤ) (x θ : AddCircle (1 : ℝ)) (k : ℕ) :
    fourier m (x + k • θ) = fourier m x * (fourier m θ) ^ k := by
  simp only [fourier_apply, zsmul_add, smul_comm m k, AddCircle.toCircle_add,
    AddCircle.toCircle_nsmul, Circle.coe_mul, Circle.coe_pow]

theorem fourier_irrational_ne_one {θ : ℝ} (hθ : Irrational θ)
    {m : ℤ} (hm : m ≠ 0) :
    fourier m (θ : AddCircle (1 : ℝ)) ≠ 1 := by
  intro h
  have hc : AddCircle.toCircle (m • (θ : AddCircle (1 : ℝ))) = 1 := by
    apply Subtype.ext
    exact h
  have hz : m • (θ : AddCircle (1 : ℝ)) = 0 :=
    AddCircle.injective_toCircle one_ne_zero (hc.trans AddCircle.toCircle_zero.symm)
  have hreal : (((m : ℝ) * θ : ℝ) : AddCircle (1 : ℝ)) = 0 := by
    simpa only [← AddCircle.coe_zsmul, zsmul_eq_mul] using hz
  obtain ⟨j, hj⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hreal
  exact (hθ.intCast_mul hm).ne_int j (by simpa using hj.symm)

theorem tendstoUniformly_fourier_rotation {θ : ℝ} (hθ : Irrational θ)
    {m : ℤ} (hm : m ≠ 0) :
    TendstoUniformly
      (fun n : ℕ => fun x : AddCircle (1 : ℝ) =>
        (∑ k ∈ Finset.range n, fourier m (x + k • (θ : AddCircle (1 : ℝ)))) /
          (n : ℂ))
      (fun _ => 0) atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have hr : fourier m (θ : AddCircle (1 : ℝ)) ≠ 1 := fourier_irrational_ne_one hθ hm
  have hrnorm : ‖fourier m (θ : AddCircle (1 : ℝ))‖ = 1 := Circle.norm_coe _
  have hlim := tendstoUniformlyOn_geometric_average _ hr hrnorm
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hlim) ε hε] with n hn
  intro x
  have hx : ‖fourier m x‖ ≤ 1 := le_of_eq (Circle.norm_coe _)
  simpa only [fourier_rotation_orbit] using hn (fourier m x) hx

end Invariant233

end OAI
