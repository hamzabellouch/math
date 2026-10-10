import OAI.Analysis.LipschitzHilbert.Estimates.AveragedSquareMoment
import Mathlib.MeasureTheory.Integral.Prod

namespace OAI

/-! Transfer horizontal moments through vertical averaging. In applications
the first measure is a fixed expanded vertical interval and the second is
the horizontal line interval. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace LipschitzHilbert

theorem lintegral_ofReal_average_swap {Ω Ξ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (ν : Measure Ξ) [SFinite μ] [SFinite ν]
    (F : Ω × Ξ → ℝ) (hF : Measurable F)
    (hi : ∀ x, Integrable (fun t => F (t,x)) μ)
    (h0 : ∀ z, 0 ≤ F z) :
    (∫⁻ x, ENNReal.ofReal (⨍ t, F (t,x) ∂μ) ∂ν) =
      (μ Set.univ)⁻¹ * ∫⁻ t, ∫⁻ x, ENNReal.ofReal (F (t,x)) ∂ν ∂μ := by
  simp_rw [ofReal_average (hi _) (Filter.Eventually.of_forall fun t => h0 (t,_)),
    ENNReal.div_eq_inv_mul]
  rw [lintegral_const_mul _ (hF.ennreal_ofReal.lintegral_prod_left)]
  congr 1
  exact (lintegral_lintegral_swap hF.ennreal_ofReal.aemeasurable).symm

def verticalSquareEnergy {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (V D : Ω → ℝ) : ℝ :=
  2 * ⨍ t, V t^2 + D t^2 ∂μ

theorem verticalSquareEnergy_measurable {Ω Ξ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) [SFinite μ] (V D : Ω × Ξ → ℝ)
    (hV : Measurable V) (hD : Measurable D) :
    Measurable (fun x => verticalSquareEnergy μ (fun t => V (t,x)) (fun t => D (t,x))) := by
  have h : Measurable (fun x => ∫ t, V (t,x)^2 + D (t,x)^2 ∂μ) :=
    ((hV.pow_const 2).add (hD.pow_const 2)).stronglyMeasurable.integral_prod_left'.measurable
  simpa only [verticalSquareEnergy, average_eq, smul_eq_mul] using
    (h.const_mul (μ.real univ)⁻¹).const_mul 2

theorem verticalSquareEnergy_line_moment {Ω Ξ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (ν : Measure Ξ) [IsFiniteMeasure μ] [NeZero μ] [SFinite ν]
    (V D : Ω × Ξ → ℝ) (hV : Measurable V) (hD : Measurable D) (n : ℕ)
    (hiV : ∀ x, Integrable (fun t => V (t,x)^2) μ)
    (hiD : ∀ x, Integrable (fun t => D (t,x)^2) μ)
    (hi : ∀ x, Integrable (fun t => (V (t,x)^2+D (t,x)^2)^n) μ)
    (hiVn : ∀ x, Integrable (fun t => V (t,x)^(2*n)) μ)
    (hiDn : ∀ x, Integrable (fun t => D (t,x)^(2*n)) μ)
    (C : ℝ≥0∞)
    (hline : ∀ t, (∫⁻ x, ENNReal.ofReal (V (t,x)^(2*n)+D (t,x)^(2*n)) ∂ν) ≤ C) :
    (∫⁻ x, ENNReal.ofReal
      (verticalSquareEnergy μ (fun t => V (t,x)) (fun t => D (t,x)))^n ∂ν) ≤
      (4:ℝ≥0∞)^n * C := by
  have hp (x : Ξ) := averaged_square_moment μ (fun t => V (t,x))
    (fun t => D (t,x)) n (hiV x) (hiD x) (hi x) (hiVn x) (hiDn x)
  have hnonneg (x : Ξ) : 0 ≤ verticalSquareEnergy μ (fun t => V (t,x))
      (fun t => D (t,x)) := by
    apply mul_nonneg (by norm_num)
    exact average_nonneg (fun t => add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hpow (x : Ξ) : ENNReal.ofReal
      (verticalSquareEnergy μ (fun t => V (t,x)) (fun t => D (t,x)))^n ≤
      (4:ℝ≥0∞)^n * ENNReal.ofReal (⨍ t, V (t,x)^(2*n)+D (t,x)^(2*n) ∂μ) := by
    have hfour : ENNReal.ofReal (4:ℝ) = 4 := by norm_num
    rw [← ENNReal.ofReal_pow (hnonneg x), ← hfour, ← ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 4),
      ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 4^n)]
    exact ENNReal.ofReal_le_ofReal (hp x)
  calc
    _ ≤ ∫⁻ x, (4:ℝ≥0∞)^n * ENNReal.ofReal
        (⨍ t, V (t,x)^(2*n)+D (t,x)^(2*n) ∂μ) ∂ν := lintegral_mono hpow
    _ = (4:ℝ≥0∞)^n * ((μ univ)⁻¹ *
        ∫⁻ t, ∫⁻ x, ENNReal.ofReal (V (t,x)^(2*n)+D (t,x)^(2*n)) ∂ν ∂μ) := by
      rw [lintegral_const_mul' _ _ (by finiteness)]
      congr 1
      apply lintegral_ofReal_average_swap μ ν (fun z => V z^(2*n)+D z^(2*n))
        ((hV.pow_const (2*n)).add (hD.pow_const (2*n))) (fun x => (hiVn x).add (hiDn x))
      intro z
      simpa only [pow_mul] using
        add_nonneg (pow_nonneg (sq_nonneg (V z)) n) (pow_nonneg (sq_nonneg (D z)) n)
    _ ≤ (4:ℝ≥0∞)^n * ((μ univ)⁻¹ * ∫⁻ _t, C ∂μ) := by
      gcongr
      exact hline _
    _ = _ := by
      rw [lintegral_const, mul_comm C (μ univ), ← mul_assoc (μ univ)⁻¹,
        ENNReal.inv_mul_cancel (NeZero.ne (μ univ))
          (measure_ne_top μ univ), one_mul]

end LipschitzHilbert

end

end OAI
