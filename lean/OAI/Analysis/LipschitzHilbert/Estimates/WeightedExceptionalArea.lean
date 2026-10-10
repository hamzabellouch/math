import OAI.Analysis.LipschitzHilbert.Estimates.NeighborhoodGeometric
import OAI.Analysis.LipschitzHilbert.Estimates.GlobalExceptionalArea

namespace OAI

/-! Raising the box threshold by the reciprocal lattice weight gives
summable exceptional areas, with a fixed spatial decay order. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace LipschitzHilbert

theorem weighted_quarter_area_of_even_moment (X M : ℝ≥0∞) (A w : ℝ)
    (hA : 0 < A) (hw : 0 < w) (n : ℕ)
    (h : (ENNReal.ofReal (4*A/w))^(2*n)*X ≤ (ENNReal.ofReal (2*A))^(2*n)*M) :
    X ≤ (1/4:ℝ≥0∞)^n*(ENNReal.ofReal w)^(2*n)*M := by
  have heq : (ENNReal.ofReal (2*(A/w)))^(2*n)*(ENNReal.ofReal w)^(2*n) =
      (ENNReal.ofReal (2*A))^(2*n) := by
    rw [← mul_pow, ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2*(A/w))]
    congr 2
    field_simp
  have h' : (ENNReal.ofReal (4*(A/w)))^(2*n)*X ≤
      (ENNReal.ofReal (2*(A/w)))^(2*n)*((ENNReal.ofReal w)^(2*n)*M) := by
    rw [← mul_assoc, heq]
    rw [show 4*(A/w) = 4*A/w by ring]
    exact h
  have hp := quarter_area_of_even_moment X ((ENNReal.ofReal w)^(2*n)*M)
    (A/w) (div_pos hA hw) n h'
  simpa only [mul_assoc] using hp

theorem weighted_quarter_area_le (X M : ℝ≥0∞) (A w : ℝ)
    (hA : 0 < A) (hw : 0 < w) (hw1 : w ≤ 1) (n : ℕ) (hn : 1 ≤ n)
    (h : (ENNReal.ofReal (4*A/w))^(2*n)*X ≤ (ENNReal.ofReal (2*A))^(2*n)*M) :
    X ≤ (1/4:ℝ≥0∞)^n*ENNReal.ofReal w*M := by
  have hp : (ENNReal.ofReal w)^(2*n) ≤ ENNReal.ofReal w := by
    have hw' : ENNReal.ofReal w ≤ 1 := by exact_mod_cast ENNReal.ofReal_le_ofReal hw1
    simpa only [pow_one] using pow_le_pow_right_of_le_one' hw' (show 1 ≤ 2*n by omega)
  exact (weighted_quarter_area_of_even_moment X M A w hA hw n h).trans
    (mul_le_mul' (mul_le_mul' le_rfl hp) le_rfl)

theorem boxVariationWeight_le_one (p : ℤ × ℤ) : boxVariationWeight p ≤ 1 := by
  have h (x : ℝ) : lineEnvelope 0 1 1 x ≤ 1 := by
    simp only [lineEnvelope, sub_zero, div_one, pow_one]
    exact inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg x])
  exact (mul_le_mul (h p.1) (h p.2) (lineEnvelope_nonneg _ _ _ _) (by norm_num)).trans_eq
    (one_mul _)

theorem global_weighted_even_moment_area {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (bad : ℤ × ℤ → Set Ω) (M : ℝ≥0∞) (A : ℝ) (hA : 0 < A)
    (n : ℕ) (hn : 1 ≤ n)
    (hbad : ∀ p, (ENNReal.ofReal (4*A/boxVariationWeight p))^(2*n)*μ (bad p) ≤
      (ENNReal.ofReal (2*A))^(2*n)*M) :
    μ (⋃ p, bad p) ≤ (1/4:ℝ≥0∞)^n*M*ENNReal.ofReal ((4*Real.pi)^2) := by
  apply global_exceptional_area μ bad ((1/4:ℝ≥0∞)^n*M)
  intro p
  have hp := weighted_quarter_area_le (μ (bad p)) M A (boxVariationWeight p) hA
    (boxVariationWeight_pos p) (boxVariationWeight_le_one p) n hn (hbad p)
  convert hp using 1
  ring

end LipschitzHilbert

end

end OAI
