import OAI.Analysis.LipschitzHilbert.Estimates.PolynomialMomentBound
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

namespace OAI

/-! Use a natural moment at its chosen order to obtain a geometric
exceptional-set bound. No asymptotic or unspecified tail input is assumed. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace LipschitzHilbert

theorem moment_superlevel {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (F : Ω → ℝ) (hF : Measurable F) (n : ℕ)
    (A threshold : ℝ) (ht : 0 < threshold) (M : ℝ≥0∞)
    (hm : (∫⁻ x, (ENNReal.ofReal |F x|)^n ∂μ) ≤ (ENNReal.ofReal A)^n*M) :
    μ {x | threshold ≤ |F x|} ≤
      ((ENNReal.ofReal A)/(ENNReal.ofReal threshold))^n*M := by
  have hsub : {x | threshold ≤ |F x|} ⊆
      {x | (ENNReal.ofReal threshold)^n ≤ (ENNReal.ofReal |F x|)^n} := by
    intro x hx
    exact pow_le_pow_left' (ENNReal.ofReal_le_ofReal hx) n
  have hmark := (mul_le_mul' le_rfl (measure_mono hsub)).trans
    ((mul_meas_ge_le_lintegral (hF.norm.ennreal_ofReal.pow_const n) _).trans hm)
  have he0 : (ENNReal.ofReal threshold)^n ≠ 0 :=
    pow_ne_zero n (ne_of_gt (ENNReal.ofReal_pos.mpr ht))
  have het : (ENNReal.ofReal threshold)^n ≠ ⊤ := by finiteness
  calc
    _ = ((ENNReal.ofReal threshold)^n)⁻¹ *
        ((ENNReal.ofReal threshold)^n * μ {x | threshold ≤ |F x|}) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel he0 het, one_mul]
    _ ≤ ((ENNReal.ofReal threshold)^n)⁻¹ * ((ENNReal.ofReal A)^n*M) :=
      mul_le_mul' le_rfl hmark
    _ = _ := by rw [ENNReal.div_eq_inv_mul, mul_pow, ENNReal.inv_pow]; ring

theorem moment_superlevel_quarter {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (F : Ω → ℝ) (hF : Measurable F) (n : ℕ)
    (A : ℝ) (hA : 0 < A) (M : ℝ≥0∞)
    (hm : (∫⁻ x, (ENNReal.ofReal |F x|)^n ∂μ) ≤ (ENNReal.ofReal A)^n*M) :
    μ {x | 4*A ≤ |F x|} ≤ (1/4:ℝ≥0∞)^n*M := by
  have h := moment_superlevel μ F hF n A (4*A) (by positivity) M hm
  have hr : (ENNReal.ofReal A)/(ENNReal.ofReal (4*A)) = (1/4:ℝ≥0∞) := by
    rw [← ENNReal.ofReal_div_of_pos (by positivity : 0 < 4*A)]
    have ha : A/(4*A) = (1/4:ℝ) := by field_simp [hA.ne']
    rw [ha]
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<4)]
    norm_num
  simpa only [hr] using h

theorem quarter_pow_exp (n : ℕ) :
    (1/4:ℝ)^n = Real.exp (-(Real.log 4)*(n:ℝ)) := by
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num),
    Real.log_div (by norm_num : (1:ℝ) ≠ 0) (by norm_num : (4:ℝ) ≠ 0), Real.log_one]
  congr 1
  ring

end LipschitzHilbert

end

end OAI
