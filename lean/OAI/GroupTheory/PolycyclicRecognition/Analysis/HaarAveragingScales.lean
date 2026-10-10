import OAI.GroupTheory.PolycyclicRecognition.Analysis.HaarAveraging
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialTripling

namespace OAI

/-! # Haar averaging along arbitrarily large good volume scales -/

namespace PolycyclicRecognition

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal NNReal

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]

/-- One sufficiently large good radius for each pair of compact sets is
enough; the tripling bound need not hold at every large radius. -/
theorem haar_averaging_at_unbounded_scales
    (μ ρ : Measure G) [SFinite μ] [SFinite ρ]
    [IsInvInvariant μ] [IsMulRightInvariant μ]
    (ℓ : GroupSeminorm G) (hℓ : Measurable ℓ)
    {J : Type*} (E : J → Set G) (a : J → ℝ≥0∞)
    (hE : ∀ j, MeasurableSet (E j))
    (hbounded : ∀ j, ∃ R : ℝ, ∀ e ∈ E j, ℓ e ≤ R)
    {K D : ℝ≥0∞} (hK : K ≠ ∞)
    (hlower : ∀ j z, a j ≤ K * ρ (leftTranslate (E j) z))
    (hupper : ∀ j z, ρ (leftTranslate (E j) z) ≤ K * a j)
    (hballs : ∀ R : ℝ, ∃ T : ℝ, R ≤ T ∧
      μ (lengthBall ℓ T) ≠ 0 ∧ μ (lengthBall ℓ T) ≠ ∞ ∧
      μ (lengthBall ℓ (3 * T)) ≤ D * μ (lengthBall ℓ T)) :
    ∀ j k, a j * μ (E k) ≤ (K * K * D) * a k * μ (E j) := by
  intro j k
  obtain ⟨Rj, hj⟩ := hbounded j
  obtain ⟨Rk, hk⟩ := hbounded k
  obtain ⟨T, hT, hT0, hTfinite, htripling⟩ := hballs (max Rj Rk)
  exact translated_mass_comparison_at_radius μ ρ ℓ hℓ (hE j) (hE k)
    (fun e he => (hj e he).trans ((le_max_left _ _).trans hT))
    (fun e he => (hk e he).trans ((le_max_right _ _).trans hT))
    hK (hlower j) (hupper k) hT0 hTfinite htripling

/-- Compact boundary sets admit the same averaging comparison from
arbitrarily large radii with a common volume tripling bound. -/
theorem haar_averaging_compact_at_unbounded_scales
    [MetricSpace G] [BorelSpace G] [IsIsometricSMul G G]
    (μ ρ : Measure G) [SFinite μ] [SFinite ρ]
    [IsInvInvariant μ] [IsMulRightInvariant μ]
    {J : Type*} (E : J → Set G) (a : J → ℝ≥0∞)
    (hE : ∀ j, IsCompact (E j)) {K D : ℝ≥0∞} (hK : K ≠ ∞)
    (hlower : ∀ j z, a j ≤ K * ρ (leftTranslate (E j) z))
    (hupper : ∀ j z, ρ (leftTranslate (E j) z) ≤ K * a j)
    (hballs : ∀ R : ℝ, ∃ T : ℝ, R ≤ T ∧
      μ (Metric.ball 1 T) ≠ 0 ∧ μ (Metric.ball 1 T) ≠ ∞ ∧
      μ (Metric.ball 1 (3 * T)) ≤ D * μ (Metric.ball 1 T)) :
    ∀ j k, a j * μ (E k) ≤ (K * K * D) * a k * μ (E j) := by
  let ℓ : GroupSeminorm G := distanceLength
  have hℓ : Continuous ℓ := continuous_const.dist continuous_id
  have hb (r : ℝ) : lengthBall ℓ r = Metric.ball 1 r := by
    ext x
    change dist 1 x < r ↔ dist x 1 < r
    rw [dist_comm]
  refine haar_averaging_at_unbounded_scales μ ρ ℓ hℓ.measurable E a
    (fun j => (hE j).measurableSet) ?_ hK hlower hupper ?_
  · intro j
    obtain ⟨R, hR⟩ := (hE j).bddAbove_image hℓ.continuousOn
    exact ⟨R, fun e he => hR (mem_image_of_mem ℓ he)⟩
  · intro R
    simpa only [hb] using hballs R

/-- An upper polynomial volume bound and positivity/finiteness of balls
suffice for the compact Haar-averaging comparison. -/
theorem haar_averaging_compact_of_polynomial_volume
    [MetricSpace G] [BorelSpace G] [IsIsometricSMul G G]
    (μ ρ : Measure G) [SFinite μ] [SFinite ρ]
    [IsInvInvariant μ] [IsMulRightInvariant μ]
    {J : Type*} (E : J → Set G) (a : J → ℝ≥0∞)
    (hE : ∀ j, IsCompact (E j)) {K : ℝ≥0∞} (hK : K ≠ ∞)
    (hlower : ∀ j z, a j ≤ K * ρ (leftTranslate (E j) z))
    (hupper : ∀ j z, ρ (leftTranslate (E j) z) ≤ K * a j)
    (hballs : ∀ T : ℝ, 1 ≤ T → μ (Metric.ball 1 T) ≠ 0 ∧ μ (Metric.ball 1 T) ≠ ∞)
    {C : ℝ} (d : ℕ)
    (hvolume : ∀ T : ℝ, 1 ≤ T → (μ (Metric.ball 1 T)).toReal ≤ C * T ^ d) :
    ∀ j k, a j * μ (E k) ≤
      (K * K * ENNReal.ofReal (2 * (3 : ℝ) ^ d)) * a k * μ (E j) := by
  apply haar_averaging_compact_at_unbounded_scales μ ρ E a hE hK hlower hupper
  intro R
  obtain ⟨T, hRT, hT, htripling⟩ := polynomial_tripling_at_arbitrarily_large_radii
    (fun T => (μ (Metric.ball 1 T)).toReal) d
    (fun T hT => ENNReal.toReal_pos (hballs T hT).1 (hballs T hT).2) hvolume R
  refine ⟨T, hRT, (hballs T hT).1, (hballs T hT).2, ?_⟩
  have h3 : 1 ≤ 3 * T := by linarith
  apply (ENNReal.toReal_le_toReal (hballs (3 * T) h3).2
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hballs T hT).2)).mp
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * (3 : ℝ) ^ d)]
    using htripling

end PolycyclicRecognition

end OAI
