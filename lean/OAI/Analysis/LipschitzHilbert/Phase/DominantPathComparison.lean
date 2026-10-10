import OAI.Analysis.LipschitzHilbert.Estimates.LogEnergyGradient
import OAI.Analysis.LipschitzHilbert.Estimates.RadialShrink

namespace OAI

/-!
# Dominant-path logarithmic comparison

The numerator and path denominator are compared together, as in §9,
`pred:path-errors` and equation (src-26). The derivative cancellation is
proved from the actual logarithmic-energy derivative; the residual
child denominator is retained with its exact fractional weight.
-/

noncomputable section

namespace LipschitzHilbert

section Residual

/-- The logarithmic correction from the off-path denominator. -/
def residualLogCorrection (R a : ℝ) : ℝ := a - Real.log (Real.exp a + R)

theorem hasDerivAt_residualLogCorrection {R : ℝ} (hR : 0 ≤ R) (a : ℝ) :
    HasDerivAt (residualLogCorrection R) (R / (Real.exp a + R)) a := by
  have h := (hasDerivAt_id a).sub
    (((Real.hasDerivAt_exp a).add_const R).log (by positivity : Real.exp a + R ≠ 0))
  convert h using 1
  · rfl
  · field_simp
    ring

/-- Throughout a logarithmic-energy interval of radius `d`, the derivative
of the residual correction is at most `exp d` times its initial fraction. -/
theorem residualLogCorrection_lipschitz {R a b d : ℝ} (hR : 0 ≤ R)
    (hd : 0 ≤ d) (hab : |b - a| ≤ d) :
    |residualLogCorrection R b - residualLogCorrection R a| ≤
      (Real.exp d * R / (Real.exp a + R)) * |b - a| := by
  have hbound (v : ℝ) (hv : v ∈ Set.Icc (a - d) (a + d)) :
      ‖deriv (residualLogCorrection R) v‖ ≤ Real.exp d * R / (Real.exp a + R) := by
    rw [(hasDerivAt_residualLogCorrection hR v).deriv, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg hR (by positivity))]
    have hexp : Real.exp a ≤ Real.exp d * Real.exp v := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith [hv.1])
    have hexpd : 1 ≤ Real.exp d := Real.one_le_exp_iff.mpr hd
    apply (div_le_div_iff₀ (by positivity : 0 < Real.exp v + R)
      (by positivity : 0 < Real.exp a + R)).2
    have hden : Real.exp a + R ≤ Real.exp d * (Real.exp v + R) := by
      nlinarith [mul_nonneg hR (sub_nonneg.mpr hexpd)]
    nlinarith [mul_le_mul_of_nonneg_left hden hR]
  have ha : a ∈ Set.Icc (a - d) (a + d) := ⟨by linarith, by linarith⟩
  have hb : b ∈ Set.Icc (a - d) (a + d) := by
    have h := abs_le.mp hab
    constructor <;> linarith
  have h := (convex_Icc (a - d) (a + d)).norm_image_sub_le_of_norm_deriv_le
    (fun v _ => (hasDerivAt_residualLogCorrection hR v).differentiableAt) hbound ha hb
  simpa only [Real.norm_eq_abs] using h

theorem residualLogCorrection_le {R a : ℝ} (hR : 0 ≤ R) :
    residualLogCorrection R a ≤ -R / (Real.exp a + R) := by
  have h := Real.log_le_sub_one_of_pos
    (div_pos (Real.exp_pos a) (by positivity : 0 < Real.exp a + R))
  rw [Real.log_div (Real.exp_pos a).ne' (by positivity : Real.exp a + R ≠ 0),
    Real.log_exp] at h
  have heq : Real.exp a / (Real.exp a + R) - 1 = -R / (Real.exp a + R) := by
    field_simp
    ring
  simpa only [residualLogCorrection, heq] using h

end Residual

section Normed

variable {E : Type*} [NormedAddCommGroup E]

/-- The off-path fraction of the complete child denominator. -/
def residualFraction (p R : ℝ) (Y : E) : ℝ := R / (1 + ‖Y‖ ^ p + R)

theorem residualFraction_nonneg {p R : ℝ} (hR : 0 ≤ R) (Y : E) :
    0 ≤ residualFraction p R Y := by
  unfold residualFraction
  positivity

theorem residual_log_energy_change {p R : ℝ} (hp : 1 ≤ p) (hR : 0 ≤ R) (Y Y' : E) :
    residualLogCorrection R (logEnergy p Y') - residualLogCorrection R (logEnergy p Y) ≤
      Real.exp (p * ‖Y' - Y‖) * p * ‖Y' - Y‖ * residualFraction p R Y := by
  have hp0 : 0 ≤ p := by linarith
  have hlog := logEnergy_lipschitz hp Y' Y
  have h := residualLogCorrection_lipschitz hR (mul_nonneg hp0 (norm_nonneg _)) hlog
  have hexp : Real.exp (logEnergy p Y) = 1 + ‖Y‖ ^ p := by
    unfold logEnergy
    exact Real.exp_log (by positivity)
  rw [hexp] at h
  have hnonneg : 0 ≤ Real.exp (p * ‖Y' - Y‖) * R / (1 + ‖Y‖ ^ p + R) := by positivity
  calc
    _ ≤ |residualLogCorrection R (logEnergy p Y') - residualLogCorrection R (logEnergy p Y)| := le_abs_self _
    _ ≤ (Real.exp (p * ‖Y' - Y‖) * R / (1 + ‖Y‖ ^ p + R)) * |logEnergy p Y' - logEnergy p Y| := h
    _ ≤ (Real.exp (p * ‖Y' - Y‖) * R / (1 + ‖Y‖ ^ p + R)) * (p * ‖Y' - Y‖) :=
      mul_le_mul_of_nonneg_left hlog hnonneg
    _ = _ := by unfold residualFraction; ring

end Normed

section Hilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def pathCancelledLogEnergy (p C : ℝ) (Z V : E) : ℝ :=
  logEnergy p (C • V + Z) - logEnergy p V

/-- Exact separation of the path denominator and the residual child mass. -/
theorem log_path_ratio_eq {p C R : ℝ} (hR : 0 ≤ R) (Y Z : E) :
    Real.log (energyRatio p (1 + ‖Y‖ ^ p + R) (C • Y + Z)) =
      pathCancelledLogEnergy p C Z Y + residualLogCorrection R (logEnergy p Y) := by
  rw [energyRatio, Real.log_div (by positivity) (by positivity)]
  unfold pathCancelledLogEnergy residualLogCorrection logEnergy
  rw [Real.exp_log (by positivity : 0 < 1 + ‖Y‖ ^ p)]
  ring

/-- The model deficit controls the residual fraction, up to the off-path
numerator amplitude, exactly as in the second line of (src-26). -/
theorem dominant_model_deficit {p C R : ℝ} (hp : 1 ≤ p) (hR : 0 ≤ R)
    (hC0 : 0 ≤ C) (hC1 : C ≤ 1) (Y Z : E) :
    residualFraction p R Y - p * ‖Z‖ ≤
      -Real.log (energyRatio p (1 + ‖Y‖ ^ p + R) (C • Y + Z)) := by
  have hnorm : ‖C • Y‖ ≤ ‖Y‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC0]
    exact mul_le_of_le_one_left (norm_nonneg _) hC1
  have hbase : logEnergy p (C • Y) ≤ logEnergy p Y := by
    unfold logEnergy
    apply Real.log_le_log (by positivity)
    exact add_le_add_right (Real.rpow_le_rpow (norm_nonneg _) hnorm (by linarith)) _
  have hperturb := (abs_le.mp (logEnergy_lipschitz hp (C • Y + Z) (C • Y))).2
  simp only [add_sub_cancel_left] at hperturb
  have hres := residualLogCorrection_le (a := logEnergy p Y) hR
  have hexp : Real.exp (logEnergy p Y) = 1 + ‖Y‖ ^ p := by
    exact Real.exp_log (by positivity)
  rw [hexp, neg_div] at hres
  rw [log_path_ratio_eq hR]
  unfold pathCancelledLogEnergy residualFraction
  linarith

theorem hasFDerivAt_pathCancelledLogEnergy {p C : ℝ} (hp : 1 < p) (Z V : E) :
    HasFDerivAt (pathCancelledLogEnergy p C Z)
      (C • logEnergyDerivative p (C • V + Z) - logEnergyDerivative p V) V := by
  have h := ((hasFDerivAt_logEnergy hp (C • V + Z)).comp V
    (((hasFDerivAt_id V).const_smul C).add_const Z)).sub (hasFDerivAt_logEnergy hp V)
  convert h using 1
  · rfl
  · ext w
    simp

theorem norm_pathCancelledLogEnergy_derivative_le {p C K : ℝ} (hp : 4 ≤ p)
    (hC0 : 0 ≤ C) (hC1 : C ≤ 1) (Z V : E) (hV : ‖V‖ ≤ K) :
    ‖C • logEnergyDerivative p (C • V + Z) - logEnergyDerivative p V‖ ≤
      p * (1 - C) + 4 * p ^ 2 * ((1 - C) * K + ‖Z‖) := by
  have hmove : ‖C • V + Z - V‖ ≤ (1 - C) * K + ‖Z‖ := by
    have heq : C • V + Z - V = (C - 1) • V + Z := by simp [sub_smul]; abel
    rw [heq]
    calc
      _ ≤ ‖(C - 1) • V‖ + ‖Z‖ := norm_add_le _ _
      _ = (1 - C) * ‖V‖ + ‖Z‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonpos (by linarith : C - 1 ≤ 0)]
        ring
      _ ≤ _ := add_le_add_left (mul_le_mul_of_nonneg_left hV (by linarith)) _
  have hdiff := (logEnergyDerivative_lipschitz hp (C • V + Z) V).trans
    (mul_le_mul_of_nonneg_left hmove (by positivity))
  have heq : C • logEnergyDerivative p (C • V + Z) - logEnergyDerivative p V =
      C • (logEnergyDerivative p (C • V + Z) - logEnergyDerivative p V) +
        (C - 1) • logEnergyDerivative p V := by
    ext w
    change C * (logEnergyDerivative p (C • V + Z)) w - (logEnergyDerivative p V) w =
      C * ((logEnergyDerivative p (C • V + Z)) w - (logEnergyDerivative p V) w) +
        (C - 1) * (logEnergyDerivative p V) w
    ring
  rw [heq]
  calc
    _ ≤ ‖C • (logEnergyDerivative p (C • V + Z) - logEnergyDerivative p V)‖ +
        ‖(C - 1) • logEnergyDerivative p V‖ := norm_add_le _ _
    _ = C * ‖logEnergyDerivative p (C • V + Z) - logEnergyDerivative p V‖ +
        (1 - C) * ‖logEnergyDerivative p V‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg hC0, abs_of_nonpos (by linarith : C - 1 ≤ 0)]
      ring
    _ ≤ ‖logEnergyDerivative p (C • V + Z) - logEnergyDerivative p V‖ + (1 - C) * p := by
      exact add_le_add (mul_le_of_le_one_left (norm_nonneg _) hC1)
        (mul_le_mul_of_nonneg_left (norm_logEnergyDerivative_le (by linarith) V) (by linarith))
    _ ≤ _ := by linarith

/-- The path numerator and path denominator change together. The resulting
motion is proportional to `1-C` and the off-path amplitude. -/
theorem pathCancelledLogEnergy_lipschitz {p C K : ℝ} (hp : 4 ≤ p)
    (hC0 : 0 ≤ C) (hC1 : C ≤ 1) (Z Y Y' : E) (hY : ‖Y‖ ≤ K) (hY' : ‖Y'‖ ≤ K) :
    |pathCancelledLogEnergy p C Z Y' - pathCancelledLogEnergy p C Z Y| ≤
      (p * (1 - C) + 4 * p ^ 2 * ((1 - C) * K + ‖Z‖)) * ‖Y' - Y‖ := by
  have h := (convex_closedBall (0 : E) K).norm_image_sub_le_of_norm_fderiv_le
    (fun V _ => (hasFDerivAt_pathCancelledLogEnergy (by linarith : 1 < p) Z V).differentiableAt)
    (fun V hV => by
      rw [(hasFDerivAt_pathCancelledLogEnergy (by linarith : 1 < p) Z V).fderiv]
      exact norm_pathCancelledLogEnergy_derivative_le hp hC0 hC1 Z V
        (by simpa only [Metric.mem_closedBall, dist_zero_right] using hV))
    (by simpa only [Metric.mem_closedBall, dist_zero_right] using hY)
    (by simpa only [Metric.mem_closedBall, dist_zero_right] using hY')
  simpa only [Real.norm_eq_abs] using h

/-- The first line of (src-26), before inserting the hierarchy's motion
constants. The numerator, path cancellation, and residual fraction have
separate exact coefficients. Increasing the actual residual only helps. -/
theorem dominant_prediction_log_comparison {p C C' R R' K : ℝ}
    (hp : 4 ≤ p) (hC0 : 0 ≤ C) (hC1 : C ≤ 1) (hR : 0 ≤ R) (hRR' : R ≤ R')
    (Y Y' Z Z' : E) (hY : ‖Y‖ ≤ K) (hY' : ‖Y'‖ ≤ K) :
    Real.log (energyRatio p (1 + ‖Y'‖ ^ p + R') (C' • Y' + Z')) -
      Real.log (energyRatio p (1 + ‖Y‖ ^ p + R) (C • Y + Z)) ≤
      p * (|C' - C| * ‖Y'‖ + ‖Z' - Z‖) +
        (p * (1 - C) + 4 * p ^ 2 * ((1 - C) * K + ‖Z‖)) * ‖Y' - Y‖ +
        Real.exp (p * ‖Y' - Y‖) * p * ‖Y' - Y‖ * residualFraction p R Y := by
  have hp1 : 1 ≤ p := by linarith
  have hp0 : 0 ≤ p := by linarith
  have hR' : 0 ≤ R' := hR.trans hRR'
  have hden : 1 + ‖Y'‖ ^ p + R ≤ 1 + ‖Y'‖ ^ p + R' := by linarith
  have hmon := prediction_log_comparison hp1
    (by positivity : 0 < 1 + ‖Y'‖ ^ p + R) hden (C' • Y' + Z') (C' • Y' + Z')
  simp only [sub_self, norm_zero, mul_zero] at hmon
  have hnumMotion : ‖(C' • Y' + Z') - (C • Y' + Z)‖ ≤
      |C' - C| * ‖Y'‖ + ‖Z' - Z‖ := by
    have heq : (C' • Y' + Z') - (C • Y' + Z) = (C' - C) • Y' + (Z' - Z) := by
      simp only [sub_smul]
      abel
    rw [heq]
    simpa only [norm_smul, Real.norm_eq_abs] using norm_add_le ((C' - C) • Y') (Z' - Z)
  have hnum := ((abs_le.mp (logEnergy_lipschitz hp1 (C' • Y' + Z') (C • Y' + Z))).2).trans
    (mul_le_mul_of_nonneg_left hnumMotion hp0)
  have hpath := (abs_le.mp (pathCancelledLogEnergy_lipschitz hp hC0 hC1 Z Y Y' hY hY')).2
  have hres := residual_log_energy_change hp1 hR Y Y'
  have hid : Real.log (energyRatio p (1 + ‖Y'‖ ^ p + R) (C' • Y' + Z')) -
      Real.log (energyRatio p (1 + ‖Y‖ ^ p + R) (C • Y + Z)) =
      (logEnergy p (C' • Y' + Z') - logEnergy p (C • Y' + Z)) +
      (pathCancelledLogEnergy p C Z Y' - pathCancelledLogEnergy p C Z Y) +
      (residualLogCorrection R (logEnergy p Y') - residualLogCorrection R (logEnergy p Y)) := by
    rw [log_path_ratio_eq hR, log_path_ratio_eq hR]
    unfold pathCancelledLogEnergy
    ring
  linarith

end Hilbert

end LipschitzHilbert

end

end OAI
