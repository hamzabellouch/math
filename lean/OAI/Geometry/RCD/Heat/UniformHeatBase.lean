import OAI.Geometry.RCD.Heat.DyadicHeatAt
import OAI.Geometry.RCD.Heat.HeatBaseBounds
import OAI.Geometry.RCD.Coordinates.DyadicMeanControl

namespace OAI

/-! # Uniform finite starting bounds for actual regularized heat metrics -/

open Set Metric MeasureTheory
open scoped InnerProductSpace NNReal

noncomputable section
namespace RegularPointCoordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Scalar lower and upper bounds control a positive metric and its inverse. -/
theorem positive_equiv_norm_bounds (Q : E ≃L[ℝ] E)
    (hQ : (Q : E →L[ℝ] E).IsPositive) {a L : ℝ} (ha : 0 < a) (hL : 0 ≤ L)
    (hlow : ∀ v, a * ‖v‖ ^ 2 ≤ ⟪v, Q v⟫_ℝ)
    (hupp : ∀ v, ⟪v, Q v⟫_ℝ ≤ L * ‖v‖ ^ 2) :
    ‖(Q : E →L[ℝ] E)‖ ≤ L ∧ ‖(Q.symm : E →L[ℝ] E)‖ ≤ a⁻¹ := by
  refine ⟨symmetric_norm_le_of_quadratic _ hQ.isSymmetric hL (fun v => ?_), ?_⟩
  · rw [abs_of_nonneg (hQ.inner_nonneg_right v)]
    exact hupp v
  · apply ContinuousLinearMap.opNorm_le_bound _ (inv_pos.mpr ha).le
    intro v
    let z := Q.symm v
    have hc := hlow z
    rw [Q.apply_symm_apply] at hc
    have hi := real_inner_le_norm z v
    change ‖z‖ ≤ a⁻¹ * ‖v‖
    by_cases hz : ‖z‖ = 0
    · rw [hz]; positivity
    have hp : 0 < ‖z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    apply (le_inv_mul_iff₀ ha).mpr
    nlinarith only [hc, hi, hp]

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)
  {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel μ hQ ker)

/-- One root-time constant bounds every pole, because the cutoff energy
has unit heat mass and the same strictly positive scalar regularizer. -/
theorem exists_uniform_dyadic_heat_base {n : ℕ}
    {U : Euclidean n →L[ℝ] SobolevSpace μ hQ}
    {M : PositiveBilinearMeasure X (Euclidean n)} {κ r R lambda ρ C : ℝ}
    {p : X} {L : ℝ≥0}
    (G : ∀ v, LocalHarmonicEnergy μ hQ U M κ p r L v)
    (χ : GoodLaplacianCutoff μ hQ p ρ C) (hρr : ρ < r)
    (hR : 0 < R) (hlambda : 0 < lambda) (J : ℕ) :
    ∃ T : ℝ, 0 < T ∧ ∀ x v,
      let Q := dyadicHeatGramAt μ hQ hk U χ x hR hlambda J
      (⟪v, Q.symm v⟫_ℝ ≤ T * ‖v‖ ^ 2 ∧ ‖v‖ ^ 2 ≤ T * ⟪v, Q.symm v⟫_ℝ) ∧
      ‖v‖ ^ 2 ≤ T * ⟪v, Q v⟫_ℝ := by
  let t := (R / (2 : ℝ) ^ J) ^ 2
  have ht : 0 < t := sq_pos_of_pos (div_pos hR (by positivity))
  let a := lambda * t
  let B := (L : ℝ) ^ 2 + a
  let T := 1 + B + a⁻¹
  have ha : 0 < a := mul_pos hlambda ht
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hBT : B ≤ T := by dsimp only [T]; linarith [inv_nonneg.mpr ha.le]
  have haT : a⁻¹ ≤ T := by dsimp only [T]; linarith
  have hT : 0 < T := by dsimp only [T]; positivity
  have hχΩ : tsupport (χ.weight : X → ℝ) ⊆ ball p (2 * r) := by
    intro z hz
    have hd := χ.tsupport_subset μ hQ hz
    change dist z p < 2 * r
    change dist z p ≤ 2 * ρ at hd
    linarith
  refine ⟨T, hT, ?_⟩
  intro x v
  let Q := dyadicHeatGramAt μ hQ hk U χ x hR hlambda J
  have hpos : (Q : Euclidean n →L[ℝ] Euclidean n).IsPositive :=
    dyadicHeatGramAt_isPositive μ hQ hk U χ x hR hlambda J
  have hlow w : a * ‖w‖ ^ 2 ≤ ⟪w, Q w⟫_ℝ := by
    apply regularizedSobolevGram_coercive
    exact Filter.Eventually.of_forall fun z => mul_nonneg (χ.bounds z).1 (hk.nonneg t ht x z)
  have hupp w : ⟪w, Q w⟫_ℝ ≤ B * ‖w‖ ^ 2 := by
    have hu := (G w).heatGram_le μ hQ hk χ.weight χ.bounds (χ.hasCompactSupport μ hQ) hχΩ ht x
    change ⟪w, cutoffHeatGram μ hQ hk χ.weight.continuous
      (χ.hasCompactSupport μ hQ) U ht x lambda w⟫_ℝ ≤ _
    rw [cutoffHeatGram_energy] at hu ⊢
    dsimp only [B, a]
    nlinarith only [hu]
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
