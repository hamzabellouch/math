import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import OAI.NumberTheory.SiegelZeros.Structure.AffineFactor

namespace OAI

namespace SiegelZeros

section

namespace SiegelZerosAwei.Workers.W01

open Complex Filter Metric Set
open scoped Topology

theorem re_logFactor_le_of_product_lower {f P g : ℂ → ℂ} {z : ℂ} {F L : ℝ}
    (hfact : f z = Complex.exp (g z) * P z) (hP : P z ≠ 0)
    (hf : ‖f z‖ ≤ Real.exp F) (hmin : -L ≤ Real.log ‖P z‖) :
    (g z).re ≤ F + L := by
  have hfn : f z ≠ 0 := by rw [hfact]; exact mul_ne_zero (Complex.exp_ne_zero _) hP
  have hlog : Real.log ‖f z‖ ≤ F := (Real.log_le_iff_le_exp (norm_pos_iff.mpr hfn)).mpr hf
  have he : Real.log ‖f z‖ = (g z).re + Real.log ‖P z‖ := by
    rw [hfact, norm_mul, Complex.norm_exp,
      Real.log_mul (Real.exp_ne_zero _) (norm_ne_zero_iff.mpr hP), Real.log_exp]
  rw [he] at hlog
  linarith

theorem re_le_of_sphere_re_le {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    {R M : ℝ} (hR : 0 < R)
    (hbound : ∀ z : ℂ, ‖z‖ = R → (g z).re ≤ M)
    {z : ℂ} (hz : ‖z‖ ≤ R) : (g z).re ≤ M := by
  have hh : ‖Complex.exp (g z)‖ ≤ Real.exp M := by
    apply Complex.norm_le_of_forall_mem_frontier_norm_le (Metric.isBounded_ball : Bornology.IsBounded (ball (0 : ℂ) R))
      (Complex.differentiable_exp.comp hg).diffContOnCl
    · intro w hw
      rw [frontier_ball (0 : ℂ) (ne_of_gt hR)] at hw
      rw [Function.comp_apply, Complex.norm_exp]
      exact Real.exp_le_exp.mpr (hbound w (by simpa only [mem_sphere_iff_norm, sub_zero] using hw))
    · rw [closure_ball (0 : ℂ) (ne_of_gt hR)]
      exact mem_closedBall_zero_iff.mpr hz
  rwa [Complex.norm_exp, Real.exp_le_exp] at hh

theorem affine_of_re_circle_bounds {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (R M : ℕ → ℝ) (hR : ∀ n, 0 < R n) (hM : ∀ n, 0 < M n)
    (hRtop : Tendsto R atTop atTop)
    (hbound : ∀ n, ∀ z : ℂ, ‖z‖ = R n → (g z).re ≤ M n)
    (hlim : Tendsto (fun n => M n / (R n) ^ 2) atTop (𝓝 0)) :
    ∃ a b : ℂ, ∀ z : ℂ, g z = a + b * z := by
  apply affine_of_second_derivative_eq_zero hg
  intro c
  have hi : Tendsto (fun n => 1 / (R n) ^ 2) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_apply, one_div, inv_pow, zero_pow two_ne_zero] using
      (tendsto_inv_atTop_zero.comp hRtop).pow 2
  have htotal : Tendsto (fun n => 32 * (2 * M n + 3 * ‖g 0‖) / (R n) ^ 2)
      atTop (𝓝 (0 : ℝ)) := by
    have ht := (hlim.const_mul 64).add (hi.const_mul (96 * ‖g 0‖))
    simpa only [mul_zero, add_zero] using Filter.Tendsto.congr (fun n => by ring) ht
  apply norm_le_zero_iff.mp
  apply ge_of_tendsto htotal
  filter_upwards [hRtop.eventually (eventually_ge_atTop (4 * ‖c‖))] with n hn
  have hb : ∀ z ∈ Metric.sphere c (R n / 4), ‖g z‖ ≤ 2 * M n + 3 * ‖g 0‖ := by
    intro z hz
    have hz' : ‖z - c‖ = R n / 4 := mem_sphere_iff_norm.mp hz
    have hnz : ‖z‖ ≤ R n / 2 := by
      have hh := norm_le_norm_sub_add z c
      rw [hz'] at hh
      linarith
    apply borel_half_radius_bound hg (hR n) (hM n) _ hnz
    intro w hw
    exact re_le_of_sphere_re_le hg (hR n) (hbound n) hw.le
  have hc := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 2
    (div_pos (hR n) (by norm_num)) hg.diffContOnCl hb
  have he : (2 : ℝ) * (2 * M n + 3 * ‖g 0‖) / (R n / 4) ^ 2 =
      32 * (2 * M n + 3 * ‖g 0‖) / (R n) ^ 2 := by
    field_simp [(hR n).ne']
    ring
  simpa only [Nat.factorial_two, Nat.cast_ofNat, he] using hc

end SiegelZerosAwei.Workers.W01

end

end SiegelZeros

end OAI
