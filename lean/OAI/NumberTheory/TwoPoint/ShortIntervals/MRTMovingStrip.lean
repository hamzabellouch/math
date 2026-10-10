import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTMovingSelectedZero
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCharacterHighZeros

namespace OAI

/-! A zero-free strip deduced from two local shrinking-disk growth bounds.
The analytic growth assumption remains explicit; the proof itself is the
exact three-factor positivity argument for the actual L-functions. -/

namespace TwoPointCorrelations

open Complex
open scoped Classical

/-- Two disks of radius `3r` with logarithmic growth budget `B` give a
zero-free horizontal distance proportional to `r/B`. -/
theorem mrt_moving_zero_free : ∃ c r₀ : ℝ, 0 < c ∧ 0 < r₀ ∧
    ∀ (q : ℕ) [NeZero q], ∀ (χ : DirichletCharacter ℂ q),
    ∀ (r t B β : ℝ), 0 < r → r ≤ r₀ → 3 * r < |t| → 1 ≤ B →
      (∀ z ∈ Metric.closedBall (0 : ℂ) (15 / 16),
        ‖mrtMovingLFunction χ r t z‖ ≤ Real.exp B) →
      (∀ z ∈ Metric.closedBall (0 : ℂ) (15 / 16),
        ‖mrtMovingLFunction (χ ^ 2) r (2 * t) z‖ ≤ Real.exp B) →
      1 - c * r / B ≤ β →
        DirichletCharacter.LFunction χ ((β : ℂ) + Complex.I * (t : ℂ)) ≠ 0 := by
  obtain ⟨δ₀, hδ₀, Z, hZ, hzeta⟩ := Erdos970.uniform_bound_Z0
  let D := 3 * Z + (5 / 3 : ℝ) * mrtCharacterLogDerivativeConstant + 2
  have hC := mrtCharacterLogDerivativeConstant_pos
  have hD1 : 1 < D := by dsimp [D]; nlinarith
  have hD : 0 < D := zero_lt_one.trans hD1
  refine ⟨1 / (40 * D), min δ₀ 1, by positivity, lt_min hδ₀ zero_lt_one, ?_⟩
  intro q _ χ r t B β hr hrr ht hB hg hg2 hβ hz
  have hr1 : r ≤ 1 := hrr.trans (min_le_right _ _)
  have hrδ : r ≤ δ₀ := hrr.trans (min_le_left _ _)
  have hBp : 0 < B := zero_lt_one.trans_le hB
  let δ := r / (10 * D * B)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδr : δ ≤ r / 10 := by
    dsimp [δ]
    apply (div_le_div_iff₀ (by positivity : 0 < 10 * D * B) (by norm_num : (0 : ℝ) < 10)).mpr
    have hDB : 1 ≤ D * B := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hD1.le) (sub_nonneg.mpr hB)]
    nlinarith [mul_nonneg hr.le (sub_nonneg.mpr hDB)]
  have hδsmall : δ < δ₀ := by linarith
  have hδ1 : δ < 1 := by linarith
  have ht2 : 3 * r < |2 * t| := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith [abs_nonneg t]
  have hβ1 : β < 1 := by
    by_contra! h
    have hn : (β : ℂ) + Complex.I * (t : ℂ) ≠ 1 := by
      intro he
      have him := congrArg Complex.im he
      simp at him
      have htp : 0 < |t| := by linarith
      simp [him] at htp
    exact χ.LFunction_ne_zero_of_one_le_re (Or.inr hn) (by simpa using h) hz
  let ε := 1 - β
  have hε : 0 ≤ ε := by dsimp [ε]; linarith
  have heq : (1 / (40 * D)) * r / B = δ / 4 := by dsimp [δ]; field_simp; ring
  rw [heq] at hβ
  have hεu : ε ≤ δ / 4 := by dsimp [ε]; linarith
  have hβr : 1 - r / 4 ≤ β := by linarith
  have hc := mrt_moving_neg_logderiv_of_zero χ hr ht hBp hg
    (σ := 1 + δ) (by linarith) (by linarith) hβr hβ1.le hz
  have hs := mrt_moving_neg_logderiv (χ ^ 2) hr ht2 hBp hg2
    (σ := 1 + δ) (by linarith) (by linarith)
  have hz0 := hzeta δ hδ hδsmall
  have hp := mrtCharacter_logderiv_positivity χ (σ := 1 + δ) (by linarith) t
  have hpoint : ((1 + δ : ℝ) : ℂ) = (1 : ℂ) + (δ : ℂ) := by push_cast; rfl
  simp only [Erdos970.logDerivZeta, ← neg_div] at hz0
  rw [← hpoint] at hz0
  have hdist : 1 + δ - β = δ + ε := by dsimp [ε]; ring
  rw [hdist] at hc
  have hBr : 1 ≤ B / r := (le_div_iff₀ hr).mpr (by linarith)
  have hcost : 3 * Z + 5 * (mrtCharacterLogDerivativeConstant * B / (3 * r)) ≤
      D * (B / r) := by
    have hZbr := mul_le_mul_of_nonneg_left hBr (show 0 ≤ 3 * Z by positivity)
    have hid : 5 * (mrtCharacterLogDerivativeConstant * B / (3 * r)) =
        ((5 / 3 : ℝ) * mrtCharacterLogDerivativeConstant) * (B / r) := by ring
    rw [hid]
    dsimp [D]
    nlinarith [div_nonneg hBp.le hr.le]
  have hpos : 0 ≤ 3 / δ + D * (B / r) - 4 / (δ + ε) := by
    have hm := add_le_add
      (add_le_add (mul_le_mul_of_nonneg_left hz0 (by norm_num : (0 : ℝ) ≤ 3))
        (mul_le_mul_of_nonneg_left hc (by norm_num : (0 : ℝ) ≤ 4))) hs
    have he : 3 * (1 / δ + Z) +
        4 * (mrtCharacterLogDerivativeConstant * B / (3 * r) - 1 / (δ + ε)) +
        mrtCharacterLogDerivativeConstant * B / (3 * r) =
        3 / δ + (3 * Z + 5 * (mrtCharacterLogDerivativeConstant * B / (3 * r))) -
          4 / (δ + ε) := by ring
    rw [he] at hm
    linarith only [hp.trans hm, hcost]
  have hδeq : δ = 1 / (10 * D * (B / r)) := by dsimp [δ]; field_simp
  exact (not_lt_of_ge hpos)
    (mrt_character_zero_free_arithmetic hD (div_pos hBp hr) hδeq hε hεu)

end TwoPointCorrelations

end OAI
