import OAI.NumberTheory.Jacobsthal.Conclusions.JacobsthalBudgetSeparation
import OAI.NumberTheory.Jacobsthal.Conclusions.IteratedLogModel

namespace OAI

namespace Erdos970.NumberTheoryLean.IteratedLogScales

open _root_.Filter JacobsthalTerminalScales
open scoped Topology

noncomputable def loglog (x : ℝ) : ℝ := Real.log (Real.log (3 * x))

noncomputable def rescale (A x : ℝ) : ℝ := A * x / loglog x

theorem loglog_pos {x : ℝ} (hx : 1 ≤ x) : 0 < loglog x := by
  apply Real.log_pos
  have h3 : 1 < Real.log 3 := by
    have := Real.log_three_gt_d9
    linarith
  exact h3.trans_le (Real.log_le_log (by norm_num) (by linarith))

theorem loglog_tendsto : Tendsto loglog atTop atTop := by
  exact Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp
    (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 3)))

theorem eventual_loglog_bounds : ∀ᶠ x : ℝ in atTop,
    4 ≤ x ∧ 0 < loglog x ∧ loglog x ≤ Real.sqrt x := by
  filter_upwards [eventual_terminal_logs] with x hx
  have hx0 : 0 < x := by linarith [hx.1]
  have hl0 : 0 < Real.log x := by linarith [hx.2.1]
  have h3x : Real.log (3 * x) ≤ 2 * Real.log x := by
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hx0.ne']
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 3) (by linarith [hx.1] : 3 ≤ x)
    linarith
  have hll : loglog x ≤ Real.log (3 * x) :=
    (Real.log_le_sub_one_of_pos (Real.log_pos (by nlinarith [hx.1] : 1 < 3 * x))).trans
      (by linarith)
  exact ⟨hx.1, loglog_pos (by linarith [hx.1]),
    hll.trans (h3x.trans (by linarith [hx.2.2.2.1]))⟩

theorem eventual_rescale_lower (A : ℝ) (hA : 3 ≤ A) :
    ∀ᶠ x : ℝ in atTop, Real.sqrt (3 * x) ≤ rescale A x := by
  filter_upwards [eventual_loglog_bounds] with x hx
  have hx0 : 0 < x := by linarith [hx.1]
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hxs : x / Real.sqrt x = Real.sqrt x := by
    apply (div_eq_iff hs.ne').mpr
    nlinarith [Real.sq_sqrt hx0.le]
  have hlower : 3 * Real.sqrt x ≤ rescale A x := by
    calc
      _ = 3 * x / Real.sqrt x := by rw [mul_div_assoc, hxs]
      _ ≤ A * x / Real.sqrt x := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hA hx0.le) hs.le
      _ ≤ A * x / loglog x := div_le_div_of_nonneg_left (by positivity) hx.2.1 hx.2.2
  have hsq : Real.sqrt (3 * x) ≤ 3 * Real.sqrt x := by
    nlinarith [Real.sq_sqrt (by positivity : 0 ≤ 3 * x), Real.sqrt_nonneg (3 * x),
      Real.sq_sqrt hx0.le, Real.sqrt_nonneg x]
  exact hsq.trans hlower

theorem rescale_tendsto (A : ℝ) (hA : 3 ≤ A) : Tendsto (rescale A) atTop atTop := by
  apply tendsto_atTop_mono' atTop (eventual_rescale_lower A hA)
  exact Real.tendsto_sqrt_atTop.comp
    (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 3))

theorem eventual_loglog_le_logW (A : ℝ) (hA : 3 ≤ A) :
    ∀ᶠ x : ℝ in atTop,
      loglog x ≤ 4 * Real.log (ErdosInverseBoxHeight.sourceW (terminalTop (rescale A x))) := by
  have hu := rescale_tendsto A hA
  filter_upwards [eventual_rescale_lower A hA, eventual_loglog_bounds,
    loglog_tendsto.eventually_ge_atTop (2 * Real.log 2),
    hu.eventually eventual_terminal_logs,
    (Real.tendsto_log_atTop.comp (terminal_top_tendsto.comp hu)).eventually
      JacobsthalSourceScale.sourceW_bounds_eventually] with x hroot hx hll huLog hw
  have hx0 : 0 < x := by linarith [hx.1]
  have h3x : 0 < 3 * x := by positivity
  have hlog3x : 0 < Real.log (3 * x) := Real.log_pos (by nlinarith [hx.1])
  have hroot0 : 0 < Real.sqrt (3 * x) := Real.sqrt_pos.mpr h3x
  have hu0 : 0 < rescale A x := hroot0.trans_le hroot
  have hlogu : 0 < Real.log (rescale A x) := by linarith [huLog.2.1]
  have h1 := Real.log_le_log hroot0 hroot
  rw [Real.log_sqrt h3x.le] at h1
  have h2 := Real.log_le_log (half_pos hlog3x) h1
  rw [show Real.log (3 * x) / 2 = Real.log (3 * x) * (1 / 2) by ring,
    Real.log_mul hlog3x.ne' (by norm_num : (1 / 2 : ℝ) ≠ 0),
    Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0),
    Real.log_one] at h2
  have h3 := Real.log_le_log hlogu huLog.2.2.2.2.1
  have hL0 : 0 < Real.log (terminalTop (rescale A x)) := hlogu.trans_le huLog.2.2.2.2.1
  have h4 := Real.log_le_log (Real.sqrt_pos.mpr hL0) hw.2.1
  rw [Real.log_sqrt hL0.le] at h4
  change Real.log (Real.log (terminalTop (rescale A x))) / 2 ≤
    Real.log (ErdosInverseBoxHeight.sourceW (terminalTop (rescale A x))) at h4
  dsimp only [loglog] at hll ⊢
  linarith

end Erdos970.NumberTheoryLean.IteratedLogScales

end OAI
