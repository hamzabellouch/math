import OAI.Probability.FreeIsing.Estimates.MessageFunction

namespace OAI

noncomputable section

namespace Problem367

theorem abs_cavityMessage_tanh_le {beta : ℝ} (hbeta : 0 ≤ beta) (z : ℝ) :
    |cavityMessage (Real.tanh beta) z| ≤ beta := by
  have htheta : 0 ≤ Real.tanh beta := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg (Real.sinh_nonneg_iff.mpr hbeta) (Real.cosh_pos beta).le
  simpa only [Real.artanh_tanh] using
    cavityMessage_abs_le_artanh htheta (Real.tanh_lt_one beta) z

theorem cavityMessage_eq_half_log_cosh_ratio (beta z : ℝ) :
    cavityMessage (Real.tanh beta) z =
      (1 / 2 : ℝ) * Real.log (Real.cosh (z + beta) / Real.cosh (z - beta)) := by
  have htheta_sq : Real.tanh beta ^ 2 ≤ 1 := (Real.tanh_sq_lt_one beta).le
  have hmem := cavityMessage_argument_mem htheta_sq z
  have hratio : (1 + Real.tanh beta * Real.tanh z) /
      (1 - Real.tanh beta * Real.tanh z) =
      Real.cosh (z + beta) / Real.cosh (z - beta) := by
    apply (div_eq_div_iff (by linarith [hmem.2]) (Real.cosh_pos (z - beta)).ne').2
    rw [Real.cosh_add, Real.cosh_sub]
    simp only [Real.tanh_eq_sinh_div_cosh]
    field_simp
  rw [cavityMessage, Real.artanh_eq_half_log ⟨hmem.1.le, hmem.2.le⟩, hratio]

theorem cavityMessage_eq_log_cosh_sub (beta z : ℝ) :
    cavityMessage (Real.tanh beta) z =
      (Real.log (Real.cosh (z + beta)) - Real.log (Real.cosh (z - beta))) / 2 := by
  rw [cavityMessage_eq_half_log_cosh_ratio beta,
    Real.log_div (Real.cosh_pos (z + beta)).ne' (Real.cosh_pos (z - beta)).ne']
  ring

theorem tanh_field_difference_eq (beta z : ℝ) :
    (Real.tanh (z + beta) - Real.tanh (z - beta)) / 2 =
      Real.tanh beta * (1 - Real.tanh z ^ 2) /
        (1 - Real.tanh beta ^ 2 * Real.tanh z ^ 2) := by
  have hp := ((Real.hasDerivAt_cosh (z + beta)).comp z
    ((hasDerivAt_id z).add_const beta)).log (Real.cosh_pos (z + beta)).ne'
  have hm := ((Real.hasDerivAt_cosh (z - beta)).comp z
    ((hasDerivAt_id z).sub_const beta)).log (Real.cosh_pos (z - beta)).ne'
  simp only [id_eq, mul_one, Function.comp_apply, ← Real.tanh_eq_sinh_div_cosh] at hp hm
  have h : HasDerivAt (cavityMessage (Real.tanh beta))
      ((Real.tanh (z + beta) - Real.tanh (z - beta)) / 2) z := by
    apply ((hp.sub hm).div_const 2).congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun x => cavityMessage_eq_log_cosh_sub beta x
  simpa only [responseAttenuation, mul_div_assoc] using
    h.unique (hasDerivAt_cavityMessage (Real.tanh_sq_lt_one beta).le z)

end Problem367

end

end OAI
