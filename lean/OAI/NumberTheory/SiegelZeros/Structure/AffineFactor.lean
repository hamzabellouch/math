import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import OAI.NumberTheory.SiegelZeros.EntireFunctions.IndexedProduct

namespace OAI

namespace SiegelZeros

section

namespace SiegelZerosAwei.Workers.W01

open Complex Filter Metric
open scoped Topology

theorem log_norm_genusOneFactor {ρ z : ℂ} (hρ : ρ ≠ 0) (hz : z ≠ ρ) :
    Real.log ‖SiegelZerosAwei.W03.genusOneFactor ρ z‖ =
      Real.log ‖z - ρ‖ - Real.log ‖ρ‖ + (z / ρ).re := by
  have hlin : 1 - z / ρ = (ρ - z) / ρ := by field_simp
  have hdiff : ρ - z ≠ 0 := sub_ne_zero.mpr hz.symm
  rw [SiegelZerosAwei.W03.genusOneFactor, norm_mul, Complex.norm_exp,
    Real.log_mul (norm_ne_zero_iff.mpr (by rw [hlin]; exact div_ne_zero hdiff hρ))
      (Real.exp_ne_zero _), Real.log_exp, hlin, norm_div,
    Real.log_div (norm_ne_zero_iff.mpr hdiff) (norm_ne_zero_iff.mpr hρ), norm_sub_rev]

theorem log_norm_genusOneFactor_lower {ρ z : ℂ} {R d : ℝ}
    (hρ : ρ ≠ 0) (hd : 0 < d) (hz : ‖z‖ = R)
    (hsep : d ≤ |R - ‖ρ‖|) :
    Real.log d - Real.log ‖ρ‖ - R / ‖ρ‖ ≤
      Real.log ‖SiegelZerosAwei.W03.genusOneFactor ρ z‖ := by
  have hdist : d ≤ ‖z - ρ‖ := hsep.trans (by simpa [hz] using abs_norm_sub_norm_le z ρ)
  have hzρ : z ≠ ρ := by intro he; simp [he] at hdist; linarith
  have hlog := Real.log_le_log hd hdist
  have hre : -(R / ‖ρ‖) ≤ (z / ρ).re := by
    have ha := abs_re_le_norm (z / ρ)
    rw [norm_div, hz] at ha
    exact (abs_le.mp ha).1
  rw [log_norm_genusOneFactor hρ hzρ]
  linarith

theorem log_norm_genusOneFactor_far {ρ z : ℂ} (hρ : ρ ≠ 0)
    (hfar : 3 * ‖z‖ ≤ ‖ρ‖) :
    -(6 * (‖z‖ / ‖ρ‖) ^ 2) ≤
      Real.log ‖SiegelZerosAwei.W03.genusOneFactor ρ z‖ := by
  have hρpos : 0 < ‖ρ‖ := norm_pos_iff.mpr hρ
  have hr0 : 0 ≤ ‖z‖ / ‖ρ‖ := div_nonneg (norm_nonneg _) hρpos.le
  have hr : ‖z‖ / ‖ρ‖ ≤ (1 / 3 : ℝ) := by
    apply (div_le_iff₀ hρpos).mpr
    linarith
  have hq : ‖z / ρ‖ ≤ 1 := by rw [norm_div]; linarith
  have hb := SiegelZerosAwei.W03.norm_primaryFactor_sub_one_le hq
  change ‖SiegelZerosAwei.W03.genusOneFactor ρ z - 1‖ ≤ 3 * ‖z / ρ‖ ^ 2 at hb
  rw [norm_div] at hb
  have hsmall : ‖SiegelZerosAwei.W03.genusOneFactor ρ z - 1‖ ≤ (1 / 2 : ℝ) := by
    nlinarith
  have hlog := Complex.norm_log_one_add_half_le_self hsmall
  have hlog' : ‖Complex.log (SiegelZerosAwei.W03.genusOneFactor ρ z)‖ ≤
      (3 / 2 : ℝ) * ‖SiegelZerosAwei.W03.genusOneFactor ρ z - 1‖ := by
    rw [show (1 : ℂ) + (SiegelZerosAwei.W03.genusOneFactor ρ z - 1) =
      SiegelZerosAwei.W03.genusOneFactor ρ z by ring] at hlog
    exact hlog
  have habs := (Complex.abs_re_le_norm (Complex.log (SiegelZerosAwei.W03.genusOneFactor ρ z))).trans hlog'
  rw [Complex.log_re] at habs
  have hneg := neg_le_abs (Real.log ‖SiegelZerosAwei.W03.genusOneFactor ρ z‖)
  nlinarith [sq_nonneg (‖z‖ / ‖ρ‖)]

theorem finite_far_product_log_lower {ι : Type*} (S : Finset ι) (ρ : ι → ℂ) (z : ℂ)
    (hρ : ∀ i ∈ S, ρ i ≠ 0) (hfar : ∀ i ∈ S, 3 * ‖z‖ ≤ ‖ρ i‖) :
    -(6 * ∑ i ∈ S, (‖z‖ / ‖ρ i‖) ^ 2) ≤
      Real.log ‖∏ i ∈ S, SiegelZerosAwei.W03.genusOneFactor (ρ i) z‖ := by
  have hz (i) (hi : i ∈ S) : z ≠ ρ i := by
    intro he
    have hp := norm_pos_iff.mpr (hρ i hi)
    have hf := hfar i hi
    rw [he] at hf
    linarith
  rw [norm_prod, Real.log_prod (fun i hi => norm_ne_zero_iff.mpr
    (SiegelZerosAwei.W03.genusOneFactor_ne_zero (hρ i hi) (hz i hi)))]
  have hb := Finset.sum_le_sum (fun i hi => log_norm_genusOneFactor_far (hρ i hi) (hfar i hi))
  simpa only [Finset.sum_neg_distrib, Finset.mul_sum] using hb

theorem borel_half_radius_bound {g : ℂ → ℂ} {R M : ℝ}
    (hg : Differentiable ℂ g) (hR : 0 < R) (hM : 0 < M)
    (hre : ∀ z : ℂ, ‖z‖ < R → (g z).re ≤ M)
    {z : ℂ} (hz : ‖z‖ ≤ R / 2) :
    ‖g z‖ ≤ 2 * M + 3 * ‖g 0‖ := by
  have hzR : ‖z‖ < R := by linarith
  have hd : 0 < R - ‖z‖ := by linarith
  have hb := Complex.borelCaratheodory hM hg.differentiableOn
    (fun w hw => hre w (mem_ball_zero_iff.mp hw)) hR
    (mem_ball_zero_iff.mpr hzR)
  refine hb.trans (add_le_add ?_ ?_)
  · apply (div_le_iff₀ hd).mpr
    nlinarith
  · apply (div_le_iff₀ hd).mpr
    nlinarith [norm_nonneg (g 0)]

theorem second_derivative_eq_zero_of_circle_bounds {g : ℂ → ℂ}
    (hg : Differentiable ℂ g) (c : ℂ) (R M : ℕ → ℝ)
    (hR : ∀ n, 0 < R n)
    (hbound : ∀ n, ∀ z ∈ Metric.sphere c (R n), ‖g z‖ ≤ M n)
    (hlim : Tendsto (fun n => 2 * M n / (R n) ^ 2) atTop (𝓝 0)) :
    iteratedDeriv 2 g c = 0 := by
  apply norm_le_zero_iff.mp
  apply ge_of_tendsto' hlim
  intro n
  simpa only [Nat.factorial_two, Nat.cast_ofNat] using
    Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 2 (hR n) hg.diffContOnCl (hbound n)

theorem affine_of_second_derivative_eq_zero {g : ℂ → ℂ}
    (hg : Differentiable ℂ g) (hzero : ∀ z : ℂ, iteratedDeriv 2 g z = 0) :
    ∃ a b : ℂ, ∀ z : ℂ, g z = a + b * z := by
  have hd : Differentiable ℂ (deriv g) := hg.contDiff.differentiable_deriv_two
  have hdd : ∀ z : ℂ, deriv (deriv g) z = 0 := by
    intro z
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hzero z
  have hconst : ∀ z : ℂ, deriv g z = deriv g 0 := fun z =>
    is_const_of_deriv_eq_zero hd hdd z 0
  let f : ℂ → ℂ := fun z => g z - deriv g 0 * z
  have hf : Differentiable ℂ f := hg.sub (differentiable_id.const_mul (deriv g 0))
  have hfzero : ∀ z : ℂ, deriv f z = 0 := by
    intro z
    have hh := (hg z).hasDerivAt.fun_sub ((hasDerivAt_id z).const_mul (deriv g 0))
    simpa only [f, id_eq, hconst z, mul_one, sub_self] using hh.deriv
  refine ⟨g 0, deriv g 0, fun z => ?_⟩
  have he := is_const_of_deriv_eq_zero hf hfzero z 0
  dsimp [f] at he
  simp only [mul_zero, sub_zero] at he
  exact sub_eq_iff_eq_add.mp he

end SiegelZerosAwei.Workers.W01

end

end SiegelZeros

end OAI
