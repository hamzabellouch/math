import Mathlib
import OAI.Probability.Localization.Cells

namespace OAI
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

open MeasureTheory Metric Set
open scoped ENNReal NNReal

namespace RepeatedLocalization

lemma euclidean_unitBall_volume_le (n : ℕ) (hn : 0 < n) :
    volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) ≤
      (Real.exp 1 * Real.sqrt Real.pi / Real.sqrt n) ^ n := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hi : Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
      Real.exp (-(n : ℝ) * ‖x‖ ^ 2)) volume := by
    by_contra hh
    have hz := integral_undef hh
    rw [GaussianFourier.integral_rexp_neg_mul_sq_norm hnR] at hz
    exact (ne_of_gt (Real.rpow_pos_of_pos (div_pos Real.pi_pos hnR) _)) hz
  have hbase : volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) *
      Real.exp (-(n : ℝ)) ≤ (Real.pi / n) ^ ((n : ℝ) / 2) := by
    calc
      _ = ∫ x : EuclideanSpace ℝ (Fin n) in ball 0 1, Real.exp (-(n : ℝ)) :=
        (setIntegral_const _).symm
      _ ≤ ∫ x : EuclideanSpace ℝ (Fin n) in ball 0 1,
          Real.exp (-(n : ℝ) * ‖x‖ ^ 2) := by
        apply setIntegral_mono_on
        · exact integrableOn_const measure_ball_lt_top.ne
        · exact hi.integrableOn
        · exact measurableSet_ball
        · intro x hx
          apply Real.exp_le_exp.mpr
          have hx' : ‖x‖ < 1 := by simpa using hx
          have hsq : ‖x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg x]
          simpa using mul_le_mul_of_nonpos_left hsq (neg_nonpos.mpr hnR.le)
      _ ≤ ∫ x : EuclideanSpace ℝ (Fin n), Real.exp (-(n : ℝ) * ‖x‖ ^ 2) :=
        integral_mono_measure Measure.restrict_le_self (Filter.Eventually.of_forall
          (fun _ => (Real.exp_pos _).le)) hi
      _ = _ := by
        rw [GaussianFourier.integral_rexp_neg_mul_sq_norm hnR,
          finrank_euclideanSpace, Fintype.card_fin]
  have hexp : Real.exp (-(n : ℝ)) > 0 := Real.exp_pos _
  have hsqrt : (Real.pi / n) ^ ((n : ℝ) / 2) =
      (Real.sqrt Real.pi / Real.sqrt n) ^ n := by
    have hex : (n : ℝ) / 2 = (1 / 2) * n := by ring
    rw [hex,
      Real.rpow_mul_natCast (div_pos Real.pi_pos hnR).le,
      ← Real.sqrt_eq_rpow, Real.sqrt_div (le_of_lt Real.pi_pos)]
  have he : Real.exp (n : ℝ) = (Real.exp 1) ^ n := by
    simp
  calc
    volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) ≤
        (Real.pi / n) ^ ((n : ℝ) / 2) / Real.exp (-(n : ℝ)) :=
      (le_div_iff₀ hexp).mpr hbase
    _ = (Real.exp 1 * Real.sqrt Real.pi / Real.sqrt n)^n := by
      rw [hsqrt, Real.exp_neg, div_inv_eq_mul, he, ← mul_pow]
      congr 1
      ring

lemma euclidean_ball_volume_le (n : ℕ) (hn : 0 < n)
    (x : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r) :
    volume.real (ball x r) ≤ (r * (Real.exp 1 * Real.sqrt Real.pi) / Real.sqrt n)^n := by
  have hv := volume.addHaar_ball_of_pos x hr
  have hreal : volume.real (ball x r) = r^n * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
    simp only [measureReal_def, hv, ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hr.le _),
      finrank_euclideanSpace, Fintype.card_fin]
  rw [hreal]
  calc
    _ ≤ r^n * (Real.exp 1 * Real.sqrt Real.pi / Real.sqrt n)^n :=
      mul_le_mul_of_nonneg_left (euclidean_unitBall_volume_le n hn) (pow_nonneg hr.le _)
    _ = _ := by rw [← mul_pow]; congr 1; ring

end RepeatedLocalization

end OAI
