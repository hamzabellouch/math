import OAI.GroupTheory.PolycyclicRecognition.Analysis.VolumeExponents
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic

namespace OAI

/-! # Removing box-volume polynomial factors from separated counts -/

namespace PolycyclicRecognition

open scoped ENNReal

/-- The two polynomial box radii contribute one polynomial prefactor. -/
theorem product_box_factors_eq {B C A x t : ℝ}
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hA : 0 ≤ A) (hx : 0 ≤ x)
    (q c d e : ℕ) :
    ENNReal.ofReal B * ENNReal.ofReal (Real.exp t) *
        ENNReal.ofReal (2 * (C * x ^ q)) ^ d *
        ENNReal.ofReal (2 * (A * x ^ c)) ^ e =
      ENNReal.ofReal ((B * (2 * C) ^ d * (2 * A) ^ e) * x ^ (q * d + c * e) * Real.exp t) := by
  have h1 : 2 * (C * x ^ q) = (2 * C) * x ^ q := by ring
  have h2 : 2 * (A * x ^ c) = (2 * A) * x ^ c := by ring
  rw [← ENNReal.ofReal_pow (show 0 ≤ 2 * (C * x ^ q) by positivity),
    ← ENNReal.ofReal_pow (show 0 ≤ 2 * (A * x ^ c) by positivity),
    ← ENNReal.ofReal_mul hB,
    ← ENNReal.ofReal_mul (show 0 ≤ B * Real.exp t by positivity),
    ← ENNReal.ofReal_mul (show 0 ≤ B * Real.exp t * (2 * (C * x ^ q)) ^ d by positivity)]
  congr 1
  simp only [h1, h2, mul_pow, ← pow_mul, pow_add]
  ring

/-- Divide a separated-count inequality by its positive finite cell mass. -/
theorem card_le_of_ennreal_mul_bound {X : Type*} (s : Finset X)
    {Q : ℝ≥0∞} (hQ : 0 < Q) (hQfin : Q < ⊤) {R : ℝ} (hR : 0 ≤ R)
    (h : (s.card : ℝ≥0∞) * Q ≤ ENNReal.ofReal R) :
    (s.card : ℝ) ≤ R / Q.toReal := by
  have hQreal : 0 < Q.toReal := ENNReal.toReal_pos hQ.ne' hQfin.ne
  apply (le_div_iff₀ hQreal).mpr
  have ht := ENNReal.toReal_mono (ENNReal.ofReal_ne_top : ENNReal.ofReal R ≠ ⊤) h
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal hR] using ht

/-- The precise two-box bound yields the usual polynomial exponential
cardinality estimate with a strictly positive real constant. -/
theorem exists_real_card_bound_of_box_factors
    {Q : ℝ≥0∞} (hQ : 0 < Q) (hQfin : Q < ⊤)
    {B C A : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (q c d e : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ {X : Type*} (s : Finset X) {x t : ℝ}, 0 ≤ x →
      (s.card : ℝ≥0∞) * Q ≤ ENNReal.ofReal B * ENNReal.ofReal (Real.exp t) *
        ENNReal.ofReal (2 * (C * x ^ q)) ^ d *
        ENNReal.ofReal (2 * (A * x ^ c)) ^ e →
      (s.card : ℝ) ≤ D * x ^ (q * d + c * e) * Real.exp t := by
  let b := B * (2 * C) ^ d * (2 * A) ^ e
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hQreal : 0 < Q.toReal := ENNReal.toReal_pos hQ.ne' hQfin.ne
  refine ⟨b / Q.toReal + 1, by positivity, ?_⟩
  intro X s x t hx hbound
  rw [product_box_factors_eq hB hC hA hx] at hbound
  have h := card_le_of_ennreal_mul_bound s hQ hQfin (by positivity) hbound
  calc
    (s.card : ℝ) ≤ (b * x ^ (q * d + c * e) * Real.exp t) / Q.toReal := h
    _ = (b / Q.toReal) * x ^ (q * d + c * e) * Real.exp t := by ring
    _ ≤ _ := by gcongr; linarith

end PolycyclicRecognition

end OAI
