import OAI.NumberTheory.Ostmann.ZeroDensity.GammaInverseBound
import OAI.NumberTheory.Ostmann.ZeroDensity.LogDerivativeDiskBound

namespace OAI

/-! # A polynomial bound for the Gamma logarithmic derivative

Only the compact real strip [1/4,3/4] is needed. The proof combines the
Euler-integral upper bound, the reflection lower bound, and the disk estimate.
-/

namespace Ostmann

open Complex Metric Set

/-- Linear growth is enough after multiplication by the eighth-order Mellin decay. -/
theorem gamma_logDeriv_strip_bound : ∃ B : ℝ, 0 < B ∧ ∀ z : ℂ,
    (1 / 4 : ℝ) ≤ z.re → z.re ≤ 3 / 4 →
      ‖logDeriv Complex.Gamma z‖ ≤ B * (1 + |z.im|) := by
  obtain ⟨C, hC, hbound⟩ := gamma_positive_strip_bound (1 / 8) (7 / 8) (by norm_num)
  let K : ℝ := 2 * |Real.log C| + |Real.log Real.pi| + 1
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨32 * (K + Real.pi), by positivity, ?_⟩
  intro z hz hz'
  let g : ℂ → ℂ := fun w => Complex.Gamma (z + w)
  have hre (w : ℂ) (hw : w ∈ ball 0 (1 / 8 : ℝ)) :
      (1 / 8 : ℝ) ≤ (z + w).re ∧ (z + w).re ≤ 7 / 8 := by
    have hn : ‖w‖ < 1 / 8 := by simpa using hw
    have ha := abs_re_le_norm w
    have hl := neg_le_abs w.re
    have hu := le_abs_self w.re
    simp only [add_re]
    constructor <;> linarith
  have hgpos (w : ℂ) (hw : w ∈ ball 0 (1 / 8 : ℝ)) : 0 < (z + w).re := by
    linarith [(hre w hw).1]
  have hgd (w : ℂ) (hw : w ∈ ball 0 (1 / 8 : ℝ)) : DifferentiableAt ℂ Complex.Gamma (z + w) := by
    apply Complex.differentiableAt_Gamma
    intro n he
    have hh := congrArg Complex.re he
    simp at hh
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hp := hgpos w hw
    simp only [add_re] at hp
    linarith
  have hg : AnalyticOnNhd ℂ g (ball 0 (1 / 8 : ℝ)) := by
    intro w hw
    rw [analyticAt_iff_eventually_differentiableAt]
    filter_upwards [isOpen_ball.eventually_mem hw] with u hu
    exact (hgd u hu).comp u (differentiableAt_id.const_add z)
  have hne (w : ℂ) (hw : w ∈ ball 0 (1 / 8 : ℝ)) : g w ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (hgpos w hw)
  have hgz : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
  have hi : ‖(Complex.Gamma z)⁻¹‖ ≤ (C / Real.pi) * Real.exp (Real.pi * |z.im|) :=
    gamma_inv_norm_bound C hC.le z (by linarith)
      (hbound (1 - z) (by simp; linarith) (by simp; linarith))
  have hlogInv : -Real.log ‖Complex.Gamma z‖ ≤
      Real.log C - Real.log Real.pi + Real.pi * |z.im| := by
    calc
      _ = Real.log ‖(Complex.Gamma z)⁻¹‖ := by rw [norm_inv, Real.log_inv]
      _ ≤ Real.log ((C / Real.pi) * Real.exp (Real.pi * |z.im|)) :=
        Real.log_le_log (norm_pos_iff.mpr (inv_ne_zero hgz)) hi
      _ = _ := by rw [Real.log_mul (div_ne_zero hC.ne' Real.pi_ne_zero) (Real.exp_ne_zero _),
                      Real.log_div hC.ne' Real.pi_ne_zero, Real.log_exp]
  have hlog (w : ℂ) (hw : w ∈ ball 0 (1 / 8 : ℝ)) :
      Real.log ‖g w‖ - Real.log ‖g 0‖ ≤ K + Real.pi * |z.im| := by
    have hu : Real.log ‖g w‖ ≤ Real.log C :=
      Real.log_le_log (norm_pos_iff.mpr (hne w hw)) (hbound (z + w) (hre w hw).1 (hre w hw).2)
    simp only [g, add_zero] at *
    dsimp only [K]
    linarith [le_abs_self (Real.log C), neg_le_abs (Real.log Real.pi)]
  have hestimate := logDeriv_norm_le_of_disk g (1 / 8) (K + Real.pi * |z.im|)
    (by norm_num) (by positivity) hg hne hlog
  have hdg : HasDerivAt g (deriv Complex.Gamma z) 0 := by
    convert! (hgd 0 (mem_ball_self (by norm_num : (0 : ℝ) < 1 / 8))).hasDerivAt.comp 0
      ((hasDerivAt_id (0 : ℂ)).const_add z) using 1
    simp
  have he : logDeriv g 0 = logDeriv Complex.Gamma z := by
    simp only [logDeriv_apply, hdg.deriv, g, add_zero]
  rw [he] at hestimate
  calc
    _ ≤ 32 * (K + Real.pi * |z.im|) := by convert hestimate using 1; ring
    _ ≤ 32 * (K + Real.pi) * (1 + |z.im|) := by
      nlinarith [abs_nonneg z.im, Real.pi_pos]

end Ostmann

end OAI
