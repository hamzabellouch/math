import OAI.Geometry.RCD.Heat.UniformHeatBase

namespace OAI

/-! # Radius-independent heat-base bounds under dimensionless regularization

The regularizer is Lambda/R^2. At a fixed dyadic index its contribution
is Lambda/4^J, so the base constant is fixed before choosing R.
-/

open Set Metric MeasureTheory
open scoped InnerProductSpace NNReal

noncomputable section
namespace RegularPointCoordinates

theorem scaled_regularizer_dyadic {R Lambda : ℝ} (hR : 0 < R) (J : ℕ) :
    (Lambda / R ^ 2) * (R / (2 : ℝ) ^ J) ^ 2 = Lambda / ((2 : ℝ) ^ J) ^ 2 := by
  field_simp [hR.ne']

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)
  {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel μ hQ ker)

/-- A single inverse-metric base bound works for every physical radius
when the dimensionless regularizer and the starting index are fixed. -/
theorem exists_scaled_dyadic_heat_base (n J : ℕ) {Lambda Lbound : ℝ}
    (hLambda : 0 < Lambda) (hLbound : 0 ≤ Lbound) :
    ∃ T : ℝ, 0 < T ∧ ∀ (R : ℝ) (hR : 0 < R)
      (U : Euclidean n →L[ℝ] SobolevSpace μ hQ)
      (M : PositiveBilinearMeasure X (Euclidean n)) (κ r ρ C : ℝ) (p : X) (L : ℝ≥0)
      (_G : ∀ v, LocalHarmonicEnergy μ hQ U M κ p r L v)
      (χ : GoodLaplacianCutoff μ hQ p ρ C),
      ρ < r → (L : ℝ) ^ 2 ≤ Lbound → ∀ x v,
      let Q := dyadicHeatGramAt μ hQ hk U χ x hR (div_pos hLambda (sq_pos_of_pos hR)) J
      (⟪v, Q.symm v⟫_ℝ ≤ T * ‖v‖ ^ 2 ∧ ‖v‖ ^ 2 ≤ T * ⟪v, Q.symm v⟫_ℝ) ∧
      ‖v‖ ^ 2 ≤ T * ⟪v, Q v⟫_ℝ := by
  let a := Lambda / ((2 : ℝ) ^ J) ^ 2
  let B := Lbound + a
  let T := 1 + B + a⁻¹
  have ha : 0 < a := div_pos hLambda (by positivity)
  have hB : 0 ≤ B := add_nonneg hLbound ha.le
  have hBT : B ≤ T := by dsimp only [T]; linarith [inv_nonneg.mpr ha.le]
  have haT : a⁻¹ ≤ T := by dsimp only [T]; linarith
  refine ⟨T, by dsimp only [T]; positivity, ?_⟩
  intro R hR U M κ r ρ C p L G χ hρr hL x v Q
  have ht : 0 < (R / (2 : ℝ) ^ J) ^ 2 := sq_pos_of_pos (div_pos hR (by positivity))
  have hreg : (Lambda / R ^ 2) * (R / (2 : ℝ) ^ J) ^ 2 = a :=
    scaled_regularizer_dyadic hR J
  have hχΩ : tsupport (χ.weight : X → ℝ) ⊆ ball p (2 * r) := by
    intro z hz
    have hd := χ.tsupport_subset μ hQ hz
    change dist z p < 2 * r
    change dist z p ≤ 2 * ρ at hd
    linarith
  have hpos : (Q : Euclidean n →L[ℝ] Euclidean n).IsPositive :=
    dyadicHeatGramAt_isPositive μ hQ hk U χ x hR _ J
  have hlow (w : Euclidean n) : a * ‖w‖ ^ 2 ≤ ⟪w, Q w⟫_ℝ := by
    rw [← hreg]
    apply regularizedSobolevGram_coercive
    exact Filter.Eventually.of_forall fun z => mul_nonneg (χ.bounds z).1 (hk.nonneg _ ht x z)
  have hupp (w : Euclidean n) : ⟪w, Q w⟫_ℝ ≤ B * ‖w‖ ^ 2 := by
    have hu := (G w).heatGram_le μ hQ hk χ.weight χ.bounds (χ.hasCompactSupport μ hQ) hχΩ ht x
    change ⟪w, cutoffHeatGram μ hQ hk χ.weight.continuous
      (χ.hasCompactSupport μ hQ) U ht x (Lambda / R ^ 2) w⟫_ℝ ≤ _
    rw [cutoffHeatGram_energy] at hu ⊢
    rw [hreg]
    have hm := mul_le_mul_of_nonneg_right hL (sq_nonneg ‖w‖)
    dsimp only [B]
    nlinarith only [hu, hm]
  have hn := positive_equiv_norm_bounds Q hpos ha hB hlow hupp
  have hi := positive_equiv_inverse_comparison Q hpos v
  have hir := positive_equiv_inverse_comparison Q.symm (positive_equiv_symm Q hpos) v
  have hv := (positive_equiv_symm Q hpos).inner_nonneg_right v
  have hv' := hpos.inner_nonneg_right v
  refine ⟨⟨hi.1.trans ?_, hi.2.trans ?_⟩, ?_⟩
  · exact mul_le_mul_of_nonneg_right (hn.2.trans haT) (sq_nonneg _)
  · exact mul_le_mul_of_nonneg_right (hn.1.trans hBT) hv
  · simp only [ContinuousLinearEquiv.symm_symm] at hir
    exact hir.2.trans (mul_le_mul_of_nonneg_right (hn.2.trans haT) hv')

end RegularPointCoordinates

end

end OAI
