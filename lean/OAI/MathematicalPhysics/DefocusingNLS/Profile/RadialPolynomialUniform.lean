import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPolynomialPowerLimit
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Calculus.Deriv.Polynomial

namespace OAI

/-! Uniform evaluation and division bounds for the finite exterior expansions. -/

open Polynomial Set Filter
namespace DefocusingNLS

theorem radialPolynomial_eval_sum_bound (P : ℂ[X]) (d : ℕ) (hd : P.natDegree ≤ d)
    (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖P.eval z‖ ≤ ∑ k ∈ Finset.range (d+1), ‖P.coeff k‖ := by
  rw [eval_eq_sum_range' (Nat.lt_succ_of_le hd) z]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun k _ => ?_))
  rw [norm_mul,norm_pow]
  exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hz)

theorem radialPolynomial_eval_difference_bound (P Q : ℂ[X]) (d : ℕ)
    (hP : P.natDegree ≤ d) (hQ : Q.natDegree ≤ d) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖P.eval z-Q.eval z‖ ≤ ∑ k ∈ Finset.range (d+1), ‖P.coeff k-Q.coeff k‖ := by
  simpa only [eval_sub,coeff_sub] using
    radialPolynomial_eval_sum_bound (P-Q) d ((natDegree_sub_le _ _).trans (max_le hP hQ)) z hz

theorem radialPolynomial_eval_tendstoUniformly (P : ℕ → ℂ[X]) (Q : ℂ[X]) (d : ℕ)
    (hdeg : ∀ᶠ n in atTop, (P n).natDegree ≤ d) (hQ : Q.natDegree ≤ d)
    (hP : ∀ k, k ≤ d → Tendsto (fun n => (P n).coeff k) atTop (nhds (Q.coeff k))) :
    TendstoUniformlyOn (fun n z => (P n).eval z) (fun z => Q.eval z) atTop
      (Metric.closedBall (0 : ℂ) 1) := by
  have hs : Tendsto (fun n => ∑ k ∈ Finset.range (d+1), ‖(P n).coeff k-Q.coeff k‖)
      atTop (nhds 0) := by
    convert tendsto_finsetSum (Finset.range (d+1)) (fun k hk =>
      ((hP k (by have := Finset.mem_range.mp hk; omega)).sub tendsto_const_nhds).norm) using 1
    simp
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hdeg,hs.eventually (gt_mem_nhds hε)] with n hn he z hz
  rw [dist_comm,dist_eq_norm]
  exact (radialPolynomial_eval_difference_bound (P n) Q d hn hQ z
    (by simpa only [Metric.mem_closedBall,dist_zero_right] using hz)).trans_lt he

theorem radialPolynomial_eval_le_of_circle (P : ℂ[X]) (ε C : ℝ) (hε : 0 < ε)
    (hP : ∀ z : ℂ, ‖z‖=ε → ‖P.eval z‖ ≤ C) (z : ℂ) (hz : ‖z‖ ≤ ε) :
    ‖P.eval z‖ ≤ C := by
  apply Complex.norm_le_of_forall_mem_frontier_norm_le (f := fun z => P.eval z)
    (U := Metric.ball (0 : ℂ) ε)
    Metric.isBounded_ball P.differentiable.diffContOnCl
  · intro w hw
    apply hP
    simpa only [Metric.mem_sphere,dist_zero_right] using Metric.frontier_ball_subset_sphere hw
  · rw [closure_ball (0 : ℂ) hε.ne']
    simpa only [Metric.mem_closedBall,dist_zero_right] using hz

theorem radialPolynomial_quotient_bound (P Q : ℂ[X]) (j : ℕ) (hPQ : P=X^j*Q)
    (ε C : ℝ) (hε : 0 < ε) (hP : ∀ z : ℂ, ‖z‖=ε → ‖P.eval z‖ ≤ C)
    (z : ℂ) (hz : ‖z‖ ≤ ε) : ‖Q.eval z‖ ≤ C/ε^j := by
  apply radialPolynomial_eval_le_of_circle Q ε (C/ε^j) hε _ z hz
  intro w hw
  have hb := hP w hw
  rw [hPQ,eval_mul,eval_pow,eval_X,norm_mul,norm_pow,hw] at hb
  exact (le_div_iff₀ (pow_pos hε j)).mpr (by nlinarith)

end DefocusingNLS

end OAI
