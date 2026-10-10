import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.Tent
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.HasDerivAtLogPrimitive
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.SumIntegralErrorLipschitz

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset

namespace OrdinaryLogIntegral
open Finset

lemma tentPhase_integral (t a H : ℝ) (ha : 0 < a) (hH : 0 < H) :
    (∫ x in a..a+2*H, tentPhase t a H x) = (H⁻¹ : ℝ) • triangleMellin t a H := by
  have hc := tentPhase_continuous t a H ha hH
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := a+H)
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  have hr : (∫ x in a..a+H, tentPhase t a H x) =
      (H⁻¹ : ℝ) • (∫ x in a..a+H, ((x-a : ℝ) : ℂ)*logPhase t x) := by
    rw [← intervalIntegral.integral_smul]
    apply intervalIntegral.integral_congr
    rw [Set.uIcc_of_le (by linarith)]
    intro x hx
    rw [tentPhase, max_eq_right hx.1, tent_rising a H x hH hx]
    simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_inv]
    ring
  have hf : (∫ x in a+H..a+2*H, tentPhase t a H x) =
      (H⁻¹ : ℝ) • (∫ x in a+H..a+2*H, ((a+2*H-x : ℝ) : ℂ)*logPhase t x) := by
    rw [← intervalIntegral.integral_smul]
    apply intervalIntegral.integral_congr
    rw [Set.uIcc_of_le (by linarith)]
    intro x hx
    rw [tentPhase, max_eq_right (by linarith [hx.1]), tent_falling a H x hH hx]
    simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_inv]
    ring
  rw [hr, hf, ← smul_add]
  rfl

lemma tentPhase_integral_span (t a H s u : ℝ) (ha : 0 < a) (hH : 0 < H)
    (hs : s ≤ a) (hu : a+2*H ≤ u) :
    (∫ x in s..u, tentPhase t a H x) = (H⁻¹ : ℝ) • triangleMellin t a H := by
  have hc := tentPhase_continuous t a H ha hH
  have hl : (∫ x in s..a, tentPhase t a H x) = 0 := by
    calc
      _ = ∫ x in s..a, (0 : ℂ) := by
        apply intervalIntegral.integral_congr
        rw [Set.uIcc_of_le hs]
        exact fun x hx => tentPhase_zero_left t a H x hH hx.2
      _ = 0 := by simp
  have hr : (∫ x in a+2*H..u, tentPhase t a H x) = 0 := by
    calc
      _ = ∫ x in a+2*H..u, (0 : ℂ) := by
        apply intervalIntegral.integral_congr
        rw [Set.uIcc_of_le hu]
        exact fun x hx => tentPhase_zero_right t a H x hH hx.1
      _ = 0 := by simp
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := a)
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _), hl, zero_add,
    ← intervalIntegral.integral_add_adjacent_intervals (b := a+2*H)
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _), hr, add_zero,
    tentPhase_integral t a H ha hH]

theorem tent_progression_error (t a H d : ℝ) (N : ℕ) (ha : 0 < a) (hH : 0 < H)
    (hd : 0 < d) (hcover : a+2*H ≤ d*N) :
    ‖(∑ n ∈ range N, tentPhase t a H (d*n)) -
       ((d*H)⁻¹ : ℝ) • triangleMellin t a H‖ ≤ (N : ℝ)*d*(H⁻¹+|t|/a) := by
  have hc : Continuous (fun x : ℝ => tentPhase t a H (d*x)) :=
    (tentPhase_continuous t a H ha hH).comp (continuous_const.mul continuous_id)
  have he := sum_integral_error_lipschitz (fun x => tentPhase t a H (d*x)) 0 N
    (L := d*(H⁻¹+|t|/a)) (by positivity) hc.continuousOn
    (fun x _ y _ => by
      have hh := tentPhase_lipschitz t a H (d*x) (d*y) ha hH
      rw [← mul_sub, abs_mul, abs_of_pos hd] at hh
      nlinarith only [hh])
  simp only [zero_add] at he
  rw [intervalIntegral.integral_comp_mul_left _ (ne_of_gt hd), mul_zero,
    tentPhase_integral_span t a H 0 (d*N) ha hH ha.le hcover, smul_smul] at he
  simpa only [mul_inv_rev, mul_comm H⁻¹ d⁻¹, mul_assoc] using he

theorem tent_progression_bound (t a H d : ℝ) (N : ℕ) (ha : 0 < a) (hH : 0 < H)
    (hd : 0 < d) (hcover : a+2*H ≤ d*N) :
    ‖∑ n ∈ range N, tentPhase t a H (d*n)‖ ≤
      (a^2+2*(a+H)^2+(a+2*H)^2)/(d*H*(1+t^2)) + (N : ℝ)*d*(H⁻¹+|t|/a) := by
  have he := tent_progression_error t a H d N ha hH hd hcover
  have hm := triangleMellin_bound t a H ha hH.le
  have hp : 0 < 1+t^2 := by positivity
  have hn : ‖((d*H)⁻¹ : ℝ) • triangleMellin t a H‖ ≤
      (a^2+2*(a+H)^2+(a+2*H)^2)/(d*H*(1+t^2)) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < (d*H)⁻¹)]
    have hh : ‖triangleMellin t a H‖ ≤ (a^2+2*(a+H)^2+(a+2*H)^2)/(1+t^2) :=
      (le_div_iff₀ hp).mpr (by nlinarith only [hm])
    apply (mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ (d*H)⁻¹)).trans_eq
    field_simp
  have hh := norm_le_insert' (∑ n ∈ range N, tentPhase t a H (d*n))
    (((d*H)⁻¹ : ℝ) • triangleMellin t a H)
  nlinarith only [hh, hn, he]

end OrdinaryLogIntegral

end

end OAI
