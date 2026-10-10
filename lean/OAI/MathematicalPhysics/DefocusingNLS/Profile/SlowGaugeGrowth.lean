import OAI.MathematicalPhysics.DefocusingNLS.Profile.SlowGaugedEquation
import OAI.MathematicalPhysics.DefocusingNLS.Profile.SlowGrowth

namespace OAI

/-! The exponential envelope of the actual gauged slow solution. -/

namespace DefocusingNLS

theorem slowGauge_norm (M : ℕ) (x : ℂ) :
    ‖slowGauge M x‖ = Real.exp (-x.re/2)*‖x‖^((M : ℝ)/2) := by
  rw [slowGauge,norm_mul,Complex.norm_exp]
  have hM : (M : ℂ)/2 = (((M : ℝ)/2 : ℝ) : ℂ) := by push_cast; rfl
  rw [hM,Complex.norm_cpow_real]
  congr 2
  norm_num [Complex.div_re]

theorem gaugedSlowSolution_polynomial_envelope (q : ℂ) (M : ℕ) (hq : -1 < q.re) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℂ, 0 ≤ x.re → 1 ≤ ‖x‖ →
      ‖gaugedSlowSolution q M x‖ ≤
        C*Real.exp (-x.re/2)*‖x‖^((M : ℝ)/2+max (-q.re) 0) := by
  obtain ⟨C,hC,hbound⟩ := regularizedSlowSolution_polynomial_bound q (M+1) hq
  refine ⟨C,hC,?_⟩
  intro x hx hn
  rw [gaugedSlowSolution,norm_mul,slowGauge_norm]
  calc
    _ ≤ (Real.exp (-x.re/2)*‖x‖^((M : ℝ)/2))*(C*‖x‖^(max (-q.re) 0)) :=
      mul_le_mul_of_nonneg_left (hbound x hx hn) (by positivity)
    _ = _ := by
      rw [Real.rpow_add (by linarith : 0 < ‖x‖)]
      ring

end DefocusingNLS

end OAI
