import OAI.Geometry.RCD.Coordinates.DyadicMeanControl
import OAI.Geometry.RCD.Heat.HeatGramError

namespace OAI

/-! # Heat Gram error from directional L1 control

Quadratic-form estimates give operator estimates without a second coordinate
polarization loss. The same normalizing frame is used in the heat matrix and
in every directional error integral.
-/

open Set MeasureTheory
open scoped InnerProductSpace NNReal

noncomputable section

namespace RegularPointCoordinates

variable {X E : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- The quadratic form of the mass-centered Gram is the weighted
pointwise directional error. -/
theorem sobolevGram_sub_mass_quadratic (U : E →L[ℝ] SobolevSpace μ hQ)
    {w : X → ℝ} (hw : AEStronglyMeasurable w μ) {C : ℝ≥0}
    (hb : ∀ᵐ x ∂μ, ‖w x‖ ≤ (C : ℝ)) (hiw : Integrable w μ) (v : E) :
    ⟪v, (sobolevGram μ hQ U hw hb -
      (∫ x, w x ∂μ) • ContinuousLinearMap.id ℝ E) v⟫_ℝ =
      ∫ x, w x * (localGamma μ hQ (U v) (U v) x - ‖v‖ ^ 2) ∂μ := by
  have hi : Integrable (fun x => w x * localGamma μ hQ (U v) (U v) x) μ :=
    (localGamma_memL1 μ hQ _ _).bdd_mul hw hb
  have hgram : ⟪v, sobolevGram μ hQ U hw hb v⟫_ℝ =
      weightedGamma μ hQ w (U v) (U v) := by
    rw [real_inner_comm]
    exact sobolevGram_inner μ hQ U hw hb v v
  rw [sub_apply, inner_sub_right, smul_apply, ContinuousLinearMap.id_apply,
    inner_smul_right, real_inner_self_eq_norm_sq, hgram]
  simp only [weightedGamma, mul_sub, integral_sub hi (hiw.mul_const _), integral_mul_const]

/-- A bound in every constant direction controls the entire Gram error. -/
theorem weightedGram_sub_mass_norm_le_of_directional
    (U : E →L[ℝ] SobolevSpace μ hQ)
    {w : X → ℝ} (hw : AEStronglyMeasurable w μ) {C : ℝ≥0}
    (hb : ∀ᵐ x ∂μ, ‖w x‖ ≤ (C : ℝ)) (hiw : Integrable w μ)
    (hpos : ∀ᵐ x ∂μ, 0 ≤ w x) {ε : ℝ} (hε : 0 ≤ ε)
    (herr : ∀ v : E, (∫ x, w x * |localGamma μ hQ (U v) (U v) x - ‖v‖ ^ 2| ∂μ) ≤
      ε * ‖v‖ ^ 2) :
    ‖sobolevGram μ hQ U hw hb - (∫ x, w x ∂μ) • ContinuousLinearMap.id ℝ E‖ ≤ ε := by
  apply symmetric_norm_le_of_quadratic _
    ((sobolevGram_isSymmetric μ hQ U hw hb).sub
      (LinearMap.IsSymmetric.id.smul (by simp))) hε
  intro v
  rw [sobolevGram_sub_mass_quadratic μ hQ U hw hb hiw]
  refine (abs_integral_le_integral_abs.trans_eq ?_).trans (herr v)
  apply integral_congr_ae
  filter_upwards [hpos] with x hx
  rw [abs_mul, abs_of_nonneg hx]

variable [μ.Regular]
  {p : ℝ → X → X → ℝ} (hp : IsContinuousHeatKernel μ hQ p)
  {χ : X → ℝ} (hχ : Continuous χ) (hsχ : HasCompactSupport χ)

/-- Relative heat/mean error, including the actual conjugated scalar
regularizer. There is no extra dimension factor. -/
theorem cutoffHeatGram_conjugated_norm_le_of_directional
    (U : E →L[ℝ] SobolevSpace μ hQ) (A : E →L[ℝ] E)
    (hχpos : ∀ y, 0 ≤ χ y) {t : ℝ} (ht : 0 < t) (x : X) (lambda : ℝ)
    {ε : ℝ} (hε : 0 ≤ ε)
    (herr : ∀ v : E, (∫ y, (χ y * p t x y) *
      |localGamma μ hQ (U (A v)) (U (A v)) y - ‖v‖ ^ 2| ∂μ) ≤ ε * ‖v‖ ^ 2) :
    ‖A.adjoint.comp ((cutoffHeatGram μ hQ hp hχ hsχ U ht x lambda).comp A) -
      ContinuousLinearMap.id ℝ E‖ ≤
      ε + |(∫ y, χ y * p t x y ∂μ) - 1| + |lambda * t| * ‖A‖ ^ 2 := by
  let w := fun y => χ y * p t x y
  let m := ∫ y, w y ∂μ
  let I := ContinuousLinearMap.id ℝ E
  let hw : AEStronglyMeasurable w μ :=
    (hχ.mul (hp.continuous_right t ht x)).aestronglyMeasurable
  let hb : ∀ᵐ y ∂μ, ‖w y‖ ≤ (cutoffHeatWeightBound μ hQ hp hχ hsχ ht x : ℝ) :=
    Filter.Eventually.of_forall (cutoffHeatWeight_le μ hQ hp hχ hsχ ht x)
  let G := sobolevGram μ hQ (U.comp A) hw hb
  have he : ‖G - m • I‖ ≤ ε := weightedGram_sub_mass_norm_le_of_directional μ hQ
    (U.comp A) hw hb
    ((hχ.mul (hp.continuous_right t ht x)).integrable_of_hasCompactSupport hsχ.mul_right)
    (Filter.Eventually.of_forall fun y => mul_nonneg (hχpos y) (hp.nonneg t ht x y)) hε herr
  have hmi : ‖(m - 1) • I‖ ≤ |m - 1| := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg _) ContinuousLinearMap.norm_id_le
  have hreg : ‖(lambda * t) • A.adjoint.comp A‖ ≤ |lambda * t| * ‖A‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, ContinuousLinearMap.norm_adjoint_comp_self, pow_two]
  rw [cutoffHeatGram_conjugate]
  change ‖G + (lambda * t) • A.adjoint.comp A - I‖ ≤ _
  have heq : G + (lambda * t) • A.adjoint.comp A - I =
      (G - m • I) + (m - 1) • I + (lambda * t) • A.adjoint.comp A := by module
  rw [heq]
  exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
    (add_le_add he hmi)) hreg)

end RegularPointCoordinates

end

end OAI
