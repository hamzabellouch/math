import Mathlib
import OAI.Analysis.RieszRectifiability.Nets.FinitePairingCancellation

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology

def polynomialDecay {d : ℕ} (q : ℕ) (x : Ambient d) : ℝ := ((1 + ‖x‖) ^ q)⁻¹

theorem polynomialDecay_measurable {d : ℕ} (q : ℕ) :
    Measurable (polynomialDecay (d := d) q) := by
  unfold polynomialDecay
  fun_prop

theorem polynomialDecay_nonneg {d : ℕ} (q : ℕ) (x : Ambient d) : 0 ≤ polynomialDecay q x := by
  unfold polynomialDecay
  positivity

theorem polynomialDecay_le_one {d : ℕ} (q : ℕ) (x : Ambient d) : polynomialDecay q x ≤ 1 := by
  unfold polynomialDecay
  apply inv_le_one_of_one_le₀
  exact one_le_pow₀ (by linarith [norm_nonneg x] : (1 : ℝ) ≤ 1 + ‖x‖)

theorem polynomialDecay_eq_rpow {d : ℕ} (q : ℕ) (x : Ambient d) :
    polynomialDecay q x = (1 + ‖x‖) ^ (-(q : ℝ)) := by
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
  rfl

theorem polynomialDecay_le_far {d : ℕ} (q : ℕ) (a x : Ambient d) (hx : 0 < dist a x) :
    polynomialDecay q x ≤ (1 + ‖a‖) ^ q * inverseDistancePow q a x := by
  have hd : dist a x ≤ (1 + ‖a‖) * (1 + ‖x‖) := by
    have h : dist a x ≤ ‖a‖ + ‖x‖ := by
      rw [dist_eq_norm]
      exact norm_sub_le a x
    nlinarith [norm_nonneg a, norm_nonneg x, mul_nonneg (norm_nonneg a) (norm_nonneg x)]
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ dist a x) hd q
  rw [inverseDistancePow, ← div_eq_mul_inv]
  apply (le_div_iff₀ (pow_pos hx q)).mpr
  calc
    _ ≤ polynomialDecay q x * ((1 + ‖a‖) * (1 + ‖x‖)) ^ q :=
      mul_le_mul_of_nonneg_left hp (polynomialDecay_nonneg q x)
    _ = _ := by
      unfold polynomialDecay
      rw [mul_pow]
      field_simp

theorem polynomial_weight_integrable_from_height_tail {d : ℕ} (q : ℕ)
    (μ : Measure (Ambient d)) (f : Ambient d → ℝ) (hf : Measurable f)
    (a : Ambient d) (R : ℝ) (hR : 0 < R)
    (hnear : IntegrableOn f (ball a R) μ)
    (hfar : IntegrableOn (fun x => |f x| * inverseDistancePow q a x) (closedExterior a R) μ) :
    Integrable (fun x => |f x| * polynomialDecay q x) μ := by
  have hm : Measurable (fun x => |f x| * polynomialDecay q x) :=
    hf.abs.mul (polynomialDecay_measurable q)
  have hi : IntegrableOn (fun x => |f x| * polynomialDecay q x) (ball a R) μ := by
    apply hnear.abs.mono' hm.aestronglyMeasurable
    apply Eventually.of_forall
    intro x
    rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (polynomialDecay_nonneg q x))]
    simpa only [mul_one] using! mul_le_mul_of_nonneg_left (polynomialDecay_le_one q x) (abs_nonneg _)
  have ho : IntegrableOn (fun x => |f x| * polynomialDecay q x) (closedExterior a R) μ := by
    apply (hfar.const_mul ((1 + ‖a‖) ^ q)).mono' hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem (closedExterior_measurable a R)] with x hx
    rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (polynomialDecay_nonneg q x))]
    calc
      _ ≤ |f x| * ((1 + ‖a‖) ^ q * inverseDistancePow q a x) :=
        mul_le_mul_of_nonneg_left (polynomialDecay_le_far q a x (hR.trans_le hx)) (abs_nonneg _)
      _ = _ := by ring
  have hu := hi.union ho
  rw [closedExterior_eq_compl_ball, union_compl_self, integrableOn_univ] at hu
  exact hu

end

end RieszRectifiability

end OAI
