import OAI.Analysis.LipschitzHilbert.Phase.DominantPathComparison
import OAI.Analysis.LipschitzHilbert.Phase.PredictionBlend

namespace OAI

/-!
# Relative-drop comparison and absorption for the dominant path

The concrete path-motion bounds from §9 are substituted in the proved
logarithmic comparison. The residual fraction is then absorbed by the actual
convex blend, giving a multiplicative error proportional to the path drop.
-/

noncomputable section

namespace LipschitzHilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Equation (src-26) with explicit universal constants. `A` accounts for the
absolute constants in the hierarchy motion estimates. -/
theorem dominant_prediction_log_comparison_of_errors
    {p C C' R R' K A ε u : ℝ} (hp : 4 ≤ p) (hA : 1 ≤ A) (hK : 1 ≤ K)
    (hε : 0 ≤ ε) (hu : 0 ≤ u) (hC0 : 0 ≤ C) (hC1 : C ≤ 1)
    (hR : 0 ≤ R) (hRR' : R ≤ R') (Y Y' Z Z' : E)
    (hY : ‖Y‖ ≤ K) (hY' : ‖Y'‖ ≤ K)
    (hCdrop : 1 - C ≤ A * u) (hZ : ‖Z‖ ≤ K * u)
    (hYmove : ‖Y' - Y‖ ≤ A * ε * K) (hCmove : |C' - C| ≤ A * ε * u)
    (hZmove : ‖Z' - Z‖ ≤ A * ε * K * u)
    (hsmall : Real.exp (A * p * ε * K) ≤ 2) :
    Real.log (energyRatio p (1 + ‖Y'‖ ^ p + R') (C' • Y' + Z')) -
      Real.log (energyRatio p (1 + ‖Y‖ ^ p + R) (C • Y + Z)) ≤
      (12 * A ^ 2 * p ^ 2 * K ^ 2 * ε) * u +
        (2 * A * p * ε * K) * residualFraction p R Y := by
  have hp0 : 0 ≤ p := by linarith
  have hA0 : 0 ≤ A := by linarith
  have hK0 : 0 ≤ K := by linarith
  have hCbar : 0 ≤ 1 - C := by linarith
  have hnum : p * (|C' - C| * ‖Y'‖ + ‖Z' - Z‖) ≤ 2 * A * p * ε * K * u := by
    have hprod := mul_le_mul hCmove hY' (norm_nonneg Y') (by positivity : 0 ≤ A * ε * u)
    calc
      _ ≤ p * ((A * ε * u) * K + A * ε * K * u) :=
        mul_le_mul_of_nonneg_left (add_le_add hprod hZmove) hp0
      _ = _ := by ring
  have hpK : p ≤ p ^ 2 * K := by
    nlinarith [mul_nonneg (sq_nonneg p) (sub_nonneg.mpr hK)]
  have hfirst : p * (1 - C) ≤ A * p ^ 2 * K * u := by
    calc
      _ ≤ p * (A * u) := mul_le_mul_of_nonneg_left hCdrop hp0
      _ ≤ p ^ 2 * K * (A * u) := mul_le_mul_of_nonneg_right hpK (mul_nonneg hA0 hu)
      _ = _ := by ring
  have hsecond : 4 * p ^ 2 * ((1 - C) * K + ‖Z‖) ≤ 8 * A * p ^ 2 * K * u := by
    have hinner : (1 - C) * K + ‖Z‖ ≤ 2 * A * K * u := by
      have hc := mul_le_mul_of_nonneg_right hCdrop hK0
      have ha := mul_le_mul_of_nonneg_right hA (mul_nonneg hK0 hu)
      nlinarith
    calc
      _ ≤ 4 * p ^ 2 * (2 * A * K * u) := mul_le_mul_of_nonneg_left hinner (by positivity)
      _ = _ := by ring
  have hcore : p * (1 - C) + 4 * p ^ 2 * ((1 - C) * K + ‖Z‖) ≤ 9 * A * p ^ 2 * K * u := by
    linarith
  have hcoreTotal : (p * (1 - C) + 4 * p ^ 2 * ((1 - C) * K + ‖Z‖)) * ‖Y' - Y‖ ≤
      9 * A ^ 2 * p ^ 2 * K ^ 2 * ε * u := by
    calc
      _ ≤ (9 * A * p ^ 2 * K * u) * (A * ε * K) :=
        mul_le_mul hcore hYmove (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hApK : 1 ≤ A * p * K := by
    calc
      1 ≤ A * p := by nlinarith
      _ ≤ A * p * K := by nlinarith [mul_nonneg (mul_nonneg hA0 hp0) (sub_nonneg.mpr hK)]
  have hnumTotal : p * (|C' - C| * ‖Y'‖ + ‖Z' - Z‖) ≤
      2 * A ^ 2 * p ^ 2 * K ^ 2 * ε * u := by
    refine hnum.trans ?_
    nlinarith [mul_nonneg (show 0 ≤ 2 * A * p * ε * K * u by positivity) (sub_nonneg.mpr hApK)]
  have hmove : p * ‖Y' - Y‖ ≤ A * p * ε * K := by
    nlinarith [mul_le_mul_of_nonneg_left hYmove hp0]
  have hexp : Real.exp (p * ‖Y' - Y‖) ≤ 2 :=
    (Real.exp_le_exp.mpr hmove).trans hsmall
  have hres : Real.exp (p * ‖Y' - Y‖) * p * ‖Y' - Y‖ * residualFraction p R Y ≤
      (2 * A * p * ε * K) * residualFraction p R Y := by
    calc
      _ = Real.exp (p * ‖Y' - Y‖) * (p * ‖Y' - Y‖) * residualFraction p R Y := by ring
      _ ≤ 2 * (A * p * ε * K) * residualFraction p R Y :=
        mul_le_mul_of_nonneg_right (mul_le_mul hexp hmove (by positivity) (by norm_num))
          (residualFraction_nonneg hR Y)
      _ = _ := by ring
  have h := dominant_prediction_log_comparison (C' := C') hp hC0 hC1 hR hRR' Y Y' Z Z' hY hY'
  have hnonneg : 0 ≤ A ^ 2 * p ^ 2 * K ^ 2 * ε * u := by positivity
  nlinarith

/-- The actual dominant-path prediction is bounded by the normalized model
blend, with no surviving error proportional to the residual denominator. -/
theorem dominant_prediction_blended_domination
    {p C C' R R' K A ε u θ : ℝ} (hp : 4 ≤ p) (hA : 1 ≤ A) (hK : 1 ≤ K)
    (hε : 0 ≤ ε) (hu : 0 ≤ u) (hC0 : 0 ≤ C) (hC1 : C ≤ 1)
    (hR : 0 ≤ R) (hRR' : R ≤ R') (Y Y' Z Z' : E)
    (hY : ‖Y‖ ≤ K) (hY' : ‖Y'‖ ≤ K)
    (hCdrop : 1 - C ≤ A * u) (hZ : ‖Z‖ ≤ K * u)
    (hYmove : ‖Y' - Y‖ ≤ A * ε * K) (hCmove : |C' - C| ≤ A * ε * u)
    (hZmove : ‖Z' - Z‖ ≤ A * ε * K * u)
    (hsmall : Real.exp (A * p * ε * K) ≤ 2)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (habsorb : 2 * A * p * ε * K ≤ θ) :
    energyRatio p (1 + ‖Y'‖ ^ p + R') (C' • Y' + Z') ≤
      Real.exp ((12 * A ^ 2 * p ^ 2 * K ^ 2 * ε + θ * (p * K)) * u) *
        ((1 - θ) * energyRatio p (1 + ‖Y‖ ^ p + R) (C • Y + Z) + θ) := by
  have hR' : 0 ≤ R' := hR.trans hRR'
  have hβ := energyRatio_pos (p := p) (by positivity : 0 < 1 + ‖Y'‖ ^ p + R') (C' • Y' + Z')
  have hb := energyRatio_pos (p := p) (by positivity : 0 < 1 + ‖Y‖ ^ p + R) (C • Y + Z)
  apply blended_prediction_domination hβ hb hθ0 hθ1 (residualFraction_nonneg hR Y) habsorb
  · exact dominant_prediction_log_comparison_of_errors hp hA hK hε hu hC0 hC1 hR hRR'
      Y Y' Z Z' hY hY' hCdrop hZ hYmove hCmove hZmove hsmall
  · have hdeficit := dominant_model_deficit (by linarith : 1 ≤ p) hR hC0 hC1 Y Z
    have hmove := mul_le_mul_of_nonneg_left hZ (by linarith : 0 ≤ p)
    nlinarith

end LipschitzHilbert

end

end OAI
