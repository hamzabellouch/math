import OAI.Geometry.RCD.Harmonic.HarmonicGrams

namespace OAI

/-! # Positive regularization of genuine Sobolev Gram operators -/

open MeasureTheory
open scoped InnerProductSpace NNReal

noncomputable section

namespace RegularPointCoordinates

variable {X E : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
  (U : E →L[ℝ] SobolevSpace μ hQ)
  {w : X → ℝ} (hw : AEStronglyMeasurable w μ) {C : ℝ≥0}
  (hb : ∀ᵐ x ∂μ, ‖w x‖ ≤ (C : ℝ))

/-- In the heat construction, `w` is the cutoff heat-kernel weight and `a`
is the positive scalar regularization `lambda * t`. -/
def regularizedSobolevGram (a : ℝ) : E →L[ℝ] E :=
  sobolevGram μ hQ U hw hb + a • ContinuousLinearMap.id ℝ E

theorem regularizedSobolevGram_energy (a : ℝ) (v : E) :
    ⟪v, regularizedSobolevGram μ hQ U hw hb a v⟫_ℝ =
      (∫ x, w x * (SobolevSpace.minimalSlope μ hQ (U v) x) ^ 2 ∂μ) +
        a * ‖v‖ ^ 2 := by
  simp only [regularizedSobolevGram, add_apply,
    smul_apply, ContinuousLinearMap.id_apply,
    inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq,
    sobolevGram_energy]

theorem regularizedSobolevGram_isPositive (hwpos : ∀ᵐ x ∂μ, 0 ≤ w x)
    {a : ℝ} (ha : 0 ≤ a) :
    (regularizedSobolevGram μ hQ U hw hb a).IsPositive :=
  (sobolevGram_isPositive μ hQ U hw hb hwpos).add
    (ContinuousLinearMap.isPositive_id.smul_of_nonneg ha)

theorem regularizedSobolevGram_coercive (hwpos : ∀ᵐ x ∂μ, 0 ≤ w x)
    (a : ℝ) (v : E) :
    a * ‖v‖ ^ 2 ≤ ⟪v, regularizedSobolevGram μ hQ U hw hb a v⟫_ℝ := by
  rw [regularizedSobolevGram_energy]
  have hn : 0 ≤ ∫ x, w x * (SobolevSpace.minimalSlope μ hQ (U v) x) ^ 2 ∂μ := by
    apply integral_nonneg_of_ae
    filter_upwards [hwpos] with x hx
    exact mul_nonneg hx (sq_nonneg _)
  linarith

theorem regularizedSobolevGram_injective (hwpos : ∀ᵐ x ∂μ, 0 ≤ w x)
    {a : ℝ} (ha : 0 < a) :
    Function.Injective (regularizedSobolevGram μ hQ U hw hb a) := by
  intro v z hvz
  have hzero : regularizedSobolevGram μ hQ U hw hb a (v - z) = 0 := by
    rw [map_sub, hvz, sub_self]
  have hc := regularizedSobolevGram_coercive μ hQ U hw hb hwpos a (v - z)
  rw [hzero, inner_zero_right] at hc
  have hn : ‖v - z‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖v - z‖]
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hn))

/-- The actual inverse exists in finite dimension; it need not be added
as a hypothesis in the later heat-matrix estimates. -/
def regularizedSobolevGramEquiv [FiniteDimensional ℝ E]
    (hwpos : ∀ᵐ x ∂μ, 0 ≤ w x) {a : ℝ} (ha : 0 < a) : E ≃L[ℝ] E :=
  (LinearEquiv.ofInjectiveEndo (regularizedSobolevGram μ hQ U hw hb a).toLinearMap
    (regularizedSobolevGram_injective μ hQ U hw hb hwpos ha)).toContinuousLinearEquiv

theorem regularizedSobolevGramEquiv_apply [FiniteDimensional ℝ E]
    (hwpos : ∀ᵐ x ∂μ, 0 ≤ w x) {a : ℝ} (ha : 0 < a) (v : E) :
    regularizedSobolevGramEquiv μ hQ U hw hb hwpos ha v =
      regularizedSobolevGram μ hQ U hw hb a v := rfl

/-- The positive regularization supplies a quantitative inverse bound. -/
theorem regularizedSobolevGramEquiv_symm_norm_le [FiniteDimensional ℝ E]
    (hwpos : ∀ᵐ x ∂μ, 0 ≤ w x) {a : ℝ} (ha : 0 < a) (v : E) :
    ‖(regularizedSobolevGramEquiv μ hQ U hw hb hwpos ha).symm v‖ ≤ a⁻¹ * ‖v‖ := by
  let A := regularizedSobolevGramEquiv μ hQ U hw hb hwpos ha
  let z := A.symm v
  have hz : regularizedSobolevGram μ hQ U hw hb a z = v := A.apply_symm_apply v
  have hc := regularizedSobolevGram_coercive μ hQ U hw hb hwpos a z
  rw [hz] at hc
  have hi := (le_abs_self ⟪z, v⟫_ℝ).trans (abs_real_inner_le_norm z v)
  change ‖z‖ ≤ a⁻¹ * ‖v‖
  by_cases hzero : ‖z‖ = 0
  · rw [hzero]
    exact mul_nonneg (inv_nonneg.mpr ha.le) (norm_nonneg v)
  · have hp : 0 < ‖z‖ := lt_of_le_of_ne (norm_nonneg z) (Ne.symm hzero)
    apply (le_inv_mul_iff₀ ha).mpr
    apply (mul_le_mul_iff_right₀ hp).mp
    nlinarith only [hc, hi]

end RegularPointCoordinates

end

end OAI
