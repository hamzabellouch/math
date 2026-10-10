import OAI.Geometry.RCD.Heat.GaussianCutoffError

namespace OAI

/-! # Directional cutoff error outside the controlled normalization range -/

open Set MeasureTheory
open scoped InnerProductSpace ENNReal NNReal

noncomputable section

namespace RegularPointCoordinates

variable {X E : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

omit [ProperSpace X] [CompleteSpace E] in
/-- A raw gradient bound gives a global cutoff error budget after any
linear change of frame. No regularity is required outside the cutoff. -/
theorem cutoff_direction_error_le_raw (U : E →L[ℝ] SobolevSpace μ hQ)
    (A : E →L[ℝ] E) {s : Set X} (hsfin : μ s ≠ ∞)
    {χ : X → ℝ} (hχ : Continuous χ)
    (hχrange : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) (hχzero : ∀ x ∉ s, χ x = 0)
    {L B : ℝ} (hL : 0 ≤ L)
    (hgradient : ∀ v : E, ∀ᵐ x ∂μ.restrict s,
      localGamma μ hQ (U v) (U v) x ≤ L * ‖v‖ ^ 2)
    (hframe : ∀ v : E, ‖A v‖ ^ 2 ≤ B * ‖v‖ ^ 2) (v : E) :
    (∫ x, χ x * |localGamma μ hQ (U (A v)) (U (A v)) x - ‖v‖ ^ 2| ∂μ) ≤
      (L * B + 1) * μ.real s * ‖v‖ ^ 2 := by
  have hpoint : ∀ᵐ x ∂μ.restrict s,
      χ x * |localGamma μ hQ (U (A v)) (U (A v)) x - ‖v‖ ^ 2| ≤
        (L * B + 1) * ‖v‖ ^ 2 := by
    filter_upwards [hgradient (A v), ae_restrict_of_ae (localGamma_self μ hQ (U (A v)))]
      with x hx hself
    have hnonneg : 0 ≤ localGamma μ hQ (U (A v)) (U (A v)) x := by
      rw [hself]
      positivity
    have hu := hx.trans (mul_le_mul_of_nonneg_left (hframe v) hL)
    have habs : |localGamma μ hQ (U (A v)) (U (A v)) x - ‖v‖ ^ 2| ≤
        (L * B + 1) * ‖v‖ ^ 2 := by
      apply abs_le.mpr
      constructor <;> nlinarith [sq_nonneg ‖v‖]
    exact (mul_le_of_le_one_left (abs_nonneg _) (hχrange x).2).trans habs
  have hχb : ∀ᵐ x ∂μ, ‖χ x‖ ≤ ((1 : ℝ≥0) : ℝ) :=
    Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hχrange x).1]
      exact (hχrange x).2
  have hsupp : Function.support χ ⊆ s := by
    intro x hx
    by_contra hn
    exact hx (hχzero x hn)
  have hχi : Integrable χ μ :=
    (integrableOn_iff_integrable_of_support_subset hsupp).mp
      ((integrableOn_const hsfin (C := (1 : ℝ))).mono'
        hχ.aestronglyMeasurable.restrict (ae_restrict_of_ae hχb))
  have hi := weighted_direction_error_integrable μ hQ (U (A v)) (‖v‖ ^ 2)
    hχ.aestronglyMeasurable hχb hχi
    (Filter.Eventually.of_forall fun x => (hχrange x).1)
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun x hx => by rw [hχzero x hx, zero_mul])]
  have hb := integral_mono_ae hi.integrableOn (integrableOn_const hsfin) hpoint
  simpa only [integral_const, Measure.real, Measure.restrict_apply_univ, smul_eq_mul,
    mul_assoc, mul_left_comm] using hb

end RegularPointCoordinates

end

end OAI
