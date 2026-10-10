import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPolynomialUniform

namespace OAI

/-! Uniform convergence persists after division by an exactly cancelled monomial. -/

open Polynomial Set Filter
namespace DefocusingNLS

theorem radialPolynomial_quotient_uniform_limit (P Q : ℕ → ℂ[X]) (P₀ Q₀ : ℂ[X])
    (j : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hPQ : ∀ n, P n=X^j*Q n) (hPQ₀ : P₀=X^j*Q₀)
    (hP : TendstoUniformlyOn (fun n z => (P n).eval z) (fun z => P₀.eval z)
      atTop (Metric.closedBall (0 : ℂ) ε)) :
    TendstoUniformlyOn (fun n z => (Q n).eval z) (fun z => Q₀.eval z)
      atTop (Metric.closedBall (0 : ℂ) ε) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro η hη
  have hj : 0 < ε^j := pow_pos hε j
  have hδ : 0 < (η/2)*ε^j := mul_pos (by positivity) hj
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hP) ((η/2)*ε^j) hδ] with n hn z hz
  have hbound : ∀ w : ℂ, ‖w‖=ε → ‖(P n-P₀).eval w‖ ≤ (η/2)*ε^j := by
    intro w hw
    have he := (hn w (by simpa only [Metric.mem_closedBall,dist_zero_right] using hw.le)).le
    rw [dist_comm,dist_eq_norm] at he
    simpa only [eval_sub] using he
  have heq : P n-P₀=X^j*(Q n-Q₀) := by rw [hPQ n,hPQ₀,mul_sub]
  have hb := radialPolynomial_quotient_bound (P n-P₀) (Q n-Q₀) j heq ε
    ((η/2)*ε^j) hε hbound z (by simpa only [Metric.mem_closedBall,dist_zero_right] using hz)
  rw [mul_div_cancel_right₀ _ hj.ne'] at hb
  rw [dist_comm,dist_eq_norm]
  have hb' : ‖(Q n).eval z-Q₀.eval z‖ ≤ η/2 := by simpa only [eval_sub] using hb
  exact hb'.trans_lt (by linarith : η/2 < η)

end DefocusingNLS

end OAI
