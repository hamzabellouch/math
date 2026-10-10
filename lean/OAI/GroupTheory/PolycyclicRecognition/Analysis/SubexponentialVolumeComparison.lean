import OAI.GroupTheory.PolycyclicRecognition.Algebra.SubexponentialBounds
import OAI.GroupTheory.PolycyclicRecognition.Analysis.VolumeExponents
import OAI.GroupTheory.PolycyclicRecognition.Analysis.CoarsePackingAsymptotics

namespace OAI

/-! # Comparing exponential rates after subexponential losses -/

namespace PolycyclicRecognition

open Filter
open scoped Topology ENNReal

/-- The measurable-image loss disappears in the eventual packing comparison. -/
theorem exponent_le_of_subexponential_exp_bound {p q : ℝ} {f g : ℝ → ℝ}
    (hf : HasSubexponentialLowerBound f) (hg : HasSubexponentialUpperBound g)
    (hbound : ∀ᶠ r in atTop, f r * Real.exp (r * p) ≤ g r * Real.exp (r * q)) :
    p ≤ q := by
  by_contra h
  have hpq : q < p := lt_of_not_ge h
  let ε := (p - q) / 4
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨r, hr⟩ := ((hf ε hε).and ((hg ε hε).and
    (hbound.and (eventually_gt_atTop (0 : ℝ))))).exists
  have he : Real.exp ((p - ε) * r) ≤ Real.exp ((q + ε) * r) := calc
    _ = Real.exp (-ε * r) * Real.exp (r * p) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ f r * Real.exp (r * p) := mul_le_mul_of_nonneg_right hr.1 (Real.exp_pos _).le
    _ ≤ g r * Real.exp (r * q) := hr.2.2.1
    _ ≤ Real.exp (ε * r) * Real.exp (r * q) := mul_le_mul_of_nonneg_right hr.2.1 (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hh := Real.exp_le_exp.mp he
  have hgap : 0 < p - q - 2 * ε := by dsimp [ε]; linarith
  have hprod := mul_pos hgap hr.2.2.2
  nlinarith

/-- A fixed polynomial packing prefactor also absorbs the subexponential
loss of the successful endpoint set. -/
theorem exponent_le_of_subexponential_polynomial_bound {p q D : ℝ}
    {f : ℝ → ℝ} (hf : HasSubexponentialLowerBound f) (hD : 0 < D) (k : ℕ)
    (hbound : ∀ᶠ r in atTop,
      f r * Real.exp (r * p) ≤ D * (1 + r) ^ k * Real.exp (r * q)) : p ≤ q := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hb : ∀ᶠ r in atTop,
      1 * Real.exp (r * (p - ε)) ≤ D * (1 + r) ^ k * Real.exp (r * q) := by
    filter_upwards [hf ε hε, hbound] with r hr hb
    calc
      _ = Real.exp (-ε * r) * Real.exp (r * p) := by rw [one_mul, ← Real.exp_add]; congr 1; ring
      _ ≤ f r * Real.exp (r * p) := mul_le_mul_of_nonneg_right hr (Real.exp_pos _).le
      _ ≤ _ := hb
  have h := exponent_le_of_polynomial_exp_bound zero_lt_one hD k hb
  linarith

/-- The separated endpoint count may lose subexponential mass, as in the
successful-parameter image estimate. -/
theorem exponent_le_of_subexponential_separated_counts {p q D : ℝ}
    {f : ℝ → ℝ} (hf : HasSubexponentialLowerBound f) (hD : 0 < D)
    {Q : ℝ≥0∞} (hQ : Q < ⊤) (k : ℕ)
    (hcount : ∀ᶠ r in atTop, ∃ N : ℕ,
      ENNReal.ofReal (f r) * ENNReal.ofReal (Real.exp (r * p)) ≤ (N : ℝ≥0∞) * Q ∧
      (N : ℝ) ≤ D * (1 + r) ^ k * Real.exp (r * q)) : p ≤ q := by
  apply exponent_le_of_subexponential_polynomial_bound hf
    (show 0 < D * Q.toReal + 1 by positivity) k
  filter_upwards [hcount, hf.eventually_pos, eventually_ge_atTop (0 : ℝ)] with r hr hfpos hrpos
  obtain ⟨N, hlow, hupp⟩ := hr
  have hfinite : (N : ℝ≥0∞) * Q ≠ ⊤ := ENNReal.mul_ne_top (by simp) hQ.ne
  have hl := ENNReal.toReal_mono hfinite hlow
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hfpos.le,
    ENNReal.toReal_ofReal (Real.exp_pos _).le, ENNReal.toReal_natCast] at hl
  calc
    f r * Real.exp (r * p) ≤ (N : ℝ) * Q.toReal := hl
    _ ≤ (D * (1 + r) ^ k * Real.exp (r * q)) * Q.toReal :=
      mul_le_mul_of_nonneg_right hupp ENNReal.toReal_nonneg
    _ = (D * Q.toReal) * (1 + r) ^ k * Real.exp (r * q) := by ring
    _ ≤ _ := by gcongr; linarith

end PolycyclicRecognition

end OAI
