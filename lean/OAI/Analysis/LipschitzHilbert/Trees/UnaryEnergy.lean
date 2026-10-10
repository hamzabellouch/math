import OAI.Analysis.LipschitzHilbert.Estimates.LogEnergy
import OAI.Analysis.LipschitzHilbert.Trees.VertexIntegration

namespace OAI

/-!
# Unary residual energies

The amount is the actual `vertexAmount` from §11. Its logarithmic motion
and the small correction `log(1+h/V)` are the analytic ingredients of
the unary-segment telescope in §10, equation `src-28`.
-/

noncomputable section

namespace LipschitzHilbert

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
theorem vertexAmount_pos {n a p : ℝ} (hn : 0 < n) (A : E) :
    0 < vertexAmount n A a p := by
  unfold vertexAmount
  positivity

omit [NormedSpace ℝ E] in
theorem mass_le_vertexAmount {n a p : ℝ} (hn : 0 ≤ n) (A : E) :
    n ≤ vertexAmount n A a p := by
  unfold vertexAmount
  exact le_add_of_nonneg_right (mul_nonneg (Real.rpow_nonneg hn _) (Real.rpow_nonneg (norm_nonneg A) _))

/-- Here `mu=(a-1)/p`, so this is exactly the normalization used in §10. -/
theorem vertexAmount_eq_normalized {n a p : ℝ} (hn : 0 < n) (hp : p ≠ 0) (A : E) :
    vertexAmount n A a p = n * (1 + ‖(n ^ ((a - 1) / p - 1)) • A‖ ^ p) := by
  rw [normalized_vertex_energy_eq hn hp]
  unfold vertexAmount
  have heq : n * n ^ (a - 1 - p) = n ^ (a - p) := by
    calc
      n * n ^ (a - 1 - p) = n ^ (1 : ℝ) * n ^ (a - 1 - p) := by rw [Real.rpow_one]
      _ = n ^ ((1 : ℝ) + (a - 1 - p)) := (Real.rpow_add hn _ _).symm
      _ = n ^ (a - p) := by congr 1; ring
  rw [mul_add, mul_one, ← mul_assoc, heq]

theorem log_vertexAmount_eq {n a p : ℝ} (hn : 0 < n) (hp : p ≠ 0) (A : E) :
    Real.log (vertexAmount n A a p) = Real.log n +
      logEnergy p ((n ^ ((a - 1) / p - 1)) • A) := by
  rw [vertexAmount_eq_normalized hn hp,
    Real.log_mul hn.ne' (by positivity)]
  rfl

theorem log_vertexAmount_lipschitz {n a p : ℝ} (hn : 0 < n) (hp : 1 ≤ p) (A A' : E) :
    |Real.log (vertexAmount n A a p) - Real.log (vertexAmount n A' a p)| ≤
      p * n ^ ((a - 1) / p - 1) * ‖A - A'‖ := by
  rw [log_vertexAmount_eq hn (by linarith : p ≠ 0),
    log_vertexAmount_eq hn (by linarith : p ≠ 0), add_sub_add_left_eq_sub]
  have h := logEnergy_lipschitz hp ((n ^ ((a - 1) / p - 1)) • A)
    ((n ^ ((a - 1) / p - 1)) • A')
  rw [← smul_sub, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hn.le _)] at h
  simpa only [mul_assoc] using h

omit [NormedSpace ℝ E] in
/-- Increasing the mass and contracting the amplitude makes the amount
a subsolution, apart from the exact mass drop. -/
theorem vertexAmount_subsolution {n n' a p : ℝ} (hn' : 0 < n') (hn : n' ≤ n)
    (hap : a ≤ p) (hp : 0 ≤ p) (A A' : E) (hA : ‖A‖ ≤ ‖A'‖) :
    vertexAmount n A a p ≤ (n - n') + vertexAmount n' A' a p := by
  have hmass := Real.rpow_le_rpow_of_nonpos hn' hn (sub_nonpos.mpr hap)
  have hamp := Real.rpow_le_rpow (norm_nonneg A) hA hp
  have hprod : n ^ (a - p) * ‖A‖ ^ p ≤ n' ^ (a - p) * ‖A'‖ ^ p := by
    calc
      _ ≤ n' ^ (a - p) * ‖A‖ ^ p :=
        mul_le_mul_of_nonneg_right hmass (Real.rpow_nonneg (norm_nonneg A) _)
      _ ≤ _ := mul_le_mul_of_nonneg_left hamp (Real.rpow_nonneg hn'.le _)
  unfold vertexAmount
  linarith

private def logCorrection (h z : ℝ) : ℝ := Real.log (Real.exp z + h) - z

private theorem hasDerivAt_logCorrection {h z : ℝ} (hh : 0 ≤ h) :
    HasDerivAt (logCorrection h) (-h / (Real.exp z + h)) z := by
  change HasDerivAt (fun t : ℝ => Real.log (Real.exp t + h) - t) _ z
  have hd := (((Real.hasDerivAt_exp z).add_const h).log
    (show Real.exp z + h ≠ 0 by positivity)).sub (hasDerivAt_id z)
  have heq : -h / (Real.exp z + h) = Real.exp z / (Real.exp z + h) - 1 := by
    field_simp [show Real.exp z + h ≠ 0 by positivity]
    ring
  rw [heq]
  exact hd

private theorem logCorrection_derivative_bound {h n z : ℝ}
    (hh : 0 ≤ h) (hn : 0 < n) (hz : Real.log n ≤ z) :
    ‖deriv (logCorrection h) z‖ ≤ h / n := by
  have hexp : n ≤ Real.exp z := by
    rw [← Real.exp_log hn]
    exact Real.exp_le_exp.mpr hz
  rw [(hasDerivAt_logCorrection hh).deriv, Real.norm_eq_abs, abs_div,
    abs_neg, abs_of_nonneg hh, abs_of_pos (by positivity : 0 < Real.exp z + h)]
  exact div_le_div_of_nonneg_left hh hn (by linarith)

private theorem logCorrection_log {h V : ℝ} (hh : 0 ≤ h) (hV : 0 < V) :
    logCorrection h (Real.log V) = Real.log (1 + h / V) := by
  unfold logCorrection
  rw [Real.exp_log hV, ← Real.log_div (by positivity : V + h ≠ 0) hV.ne']
  congr 1
  field_simp [hV.ne']

/-- The residual denominator correction has Lipschitz constant `h/n`
in logarithmic coordinates whenever both amounts are at least `n`. -/
theorem log_correction_lipschitz {h n V W : ℝ} (hh : 0 ≤ h) (hn : 0 < n)
    (hV : n ≤ V) (hW : n ≤ W) :
    |Real.log (1 + h / V) - Real.log (1 + h / W)| ≤
      (h / n) * |Real.log V - Real.log W| := by
  have hVp : 0 < V := hn.trans_le hV
  have hWp : 0 < W := hn.trans_le hW
  have h := (convex_Ici (Real.log n)).norm_image_sub_le_of_norm_deriv_le
    (fun z _ => (hasDerivAt_logCorrection hh).differentiableAt)
    (fun z hz => logCorrection_derivative_bound hh hn hz)
    (Real.log_le_log hn hW) (Real.log_le_log hn hV)
  simpa only [Real.norm_eq_abs, logCorrection_log hh hVp, logCorrection_log hh hWp] using h

end LipschitzHilbert

end

end OAI
