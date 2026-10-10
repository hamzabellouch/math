import OAI.Geometry.RCD.Coordinates.RegularShiftedCentralMass

namespace OAI

/-! # Cumulative comparison for the actual pinching matrices -/

open Set Metric MeasureTheory
open scoped InnerProductSpace BigOperators

noncomputable section
namespace RegularPointCoordinates

/-- A positive rescaling of the central mass changes only the finite constant. -/
theorem central_comparison_rescale {H t mass T c : ℝ}
    (ht : 0 ≤ t) (hm : 0 ≤ mass) (hT : 0 ≤ T) (hc : 0 < c)
    (h : H ≤ T * (t + mass)) :
    H ≤ (T * (1 + c⁻¹)) * (t + c * mass) := by
  have heq : (1 + c⁻¹) * (t + c * mass) =
      (t + mass) + (c * mass + c⁻¹ * t) := by
    field_simp
    ring
  calc
    H ≤ T * (t + mass) := h
    _ ≤ T * ((t + mass) + (c * mass + c⁻¹ * t)) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity)) hT
    _ = _ := by rw [← heq]; ring

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- Actual raw masses, mean inverses and a strictly interior central heat
scale satisfy both cumulative comparisons. All matrix changes and the
reverse covering are derived from the constructed data. -/
theorem regular_patch_cumulative_comparison {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular]
    {base : X} {a κ B J C A Cχ enlargement zeta eta : ℝ}
    {ker : ℝ → X → X → ℝ}
    {hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker}
    (e : RegularProjectionEnvironment hX base hk a κ B J C A Cχ enlargement zeta eta)
    (hzeta : 0 ≤ zeta) (hzeta1 : zeta ≤ 1) (hCχ : 0 ≤ Cχ)
    (hsmall : (n : ℝ) ^ 2 * (((5 / 3 : ℝ) * ((1 / 8 : ℝ) ^ n)⁻¹) * zeta) ≤ 1 / 2)
    (hnear : (n : ℝ) ^ 2 * (((5 / 3 : ℝ) * ((1 / 2 : ℝ) ^ n)⁻¹) * zeta) ≤ 1 / 4)
    (N : ℕ) :
    ∃ Theta tau : ℝ, 0 < Theta ∧ 0 < tau ∧ ∀ epsilon : ℝ, 0 ≤ epsilon → epsilon ≤ tau →
    (∀ i, 4 * pinchingMassUnitFactor n * regularSmallMassCoefficient n Cχ *
      (zeta + |K| * (e.heat.radius / (2 : ℝ) ^ (e.heat.shift + i + 15)) ^ 2) ≤ epsilon) →
    ∀ {ι : Type*} (s : ℕ → Finset ι)
      (centers : ℕ → ι → {z : X // z ∈ ball base (e.heat.radius / 32)})
      (weight : ℕ → ι → ℝ),
    (∀ i, (s i).card ≤ N) → ∀ q, q ∈ ball base (e.heat.radius / 32) →
    (∀ i y, y ∈ s i → dist (centers i y).val q ≤
      (e.heat.radius / (2 : ℝ) ^ (e.heat.shift + i + 15)) / 12) →
    (∀ i y, y ∈ s i → dist q (centers i y).val ≤
      enlargement * (e.heat.radius / (2 : ℝ) ^ (e.heat.shift + i + 15))) →
    (∀ i y, y ∈ s i → 0 ≤ weight i y) →
    (∀ i, ∃ y ∈ s i, weight i y = 1) →
    ∀ (xi : Euclidean n) (k : ℕ),
      let D := fun i y => e.heat.pinchingMassMatrix (centers i y).val (centers i y).property
        (e.heat.shift + i)
      (‖xi‖ ^ 2 + (∑ i ∈ Finset.range k, ∑ y ∈ s i, ⟪xi, D i y xi⟫_ℝ) ≤
        Theta * ‖e.heat.frozenAt q k xi‖ ^ 2) ∧
      (‖e.heat.frozenAt q k xi‖ ^ 2 ≤ Theta *
        (‖xi‖ ^ 2 + ∑ i ∈ Finset.range k, ∑ y ∈ s i, weight i y * ⟪xi, D i y xi⟫_ℝ)) := by
  classical
  obtain ⟨T, hT, hcentral⟩ := e.heat.shifted_central_mass_comparison
  let c := patchCentralFactor n
  have hc : 0 < c := by dsimp only [c, patchCentralFactor]; positivity
  let K₀ := T * (1 + c⁻¹)
  let U := (N : ℝ) * patchEnvelopeFactor n * e.heat.envelopeConstant
  let V := (N : ℝ) * (32 * e.heat.comparisonConstant * e.heat.envelopeConstant + 4)
  have hK₀ : 0 < K₀ := mul_pos hT (by positivity)
  have hU : 0 ≤ U := by
    dsimp only [U, patchEnvelopeFactor]
    have hA := e.heat.envelopeConstant_pos
    positivity
  have hV : 0 ≤ V := by
    dsimp only [V]
    have hA := e.heat.envelopeConstant_pos
    have hC := e.heat.comparisonConstant_pos
    positivity
  let Theta := e.heat.lowerConstant + 2 * (U + V) + 4 * K₀ + 1
  let tau := min 1 (1 / (4 * K₀ * (V + 1)))
  have hTheta : 0 < Theta := by dsimp only [Theta]; linarith [e.heat.lowerConstant_pos]
  have htau : 0 < tau := lt_min zero_lt_one (by positivity)
  refine ⟨Theta, tau, hTheta, htau, ?_⟩
  intro epsilon hepsilon hetau hcoefficient ι s centers weight hcard q hq hroom henlargement hweight hcover xi k D
  have hepsilon1 : epsilon ≤ 1 := hetau.trans (min_le_left _ _)
  have habsorb : 2 * K₀ * V * epsilon ≤ 1 / 2 := by
    have h := (le_div_iff₀ (by positivity : 0 < 4 * K₀ * (V + 1))).mp
      (hetau.trans (min_le_right _ _))
    have hp := mul_nonneg hK₀.le hepsilon
    nlinarith only [h, hp]
  let Q := fun i => e.heat.heatAt q (e.heat.shift + i + 17)
  let R := fun i y => e.heat.meanAt (centers i y).val (centers i y).property (e.heat.shift + i + 15)
  let C₀ := fun i y => rawPinchingMass e.heat.mass n e.heat.radius (centers i y).val (e.heat.shift + i)
  let a₀ := fun i => (Q i).symm xi
  let z₀ := fun i y => (R i y).symm xi
  let N₀ := fun i => c • dyadicBochnerMass e.heat.mass n q e.heat.radius (e.heat.shift + i + 17)
  let H := ‖e.heat.frozenAt q k xi‖ ^ 2
  have hC₀ (i y) (_hy : y ∈ s i) : (C₀ i y).IsPositive := by
    apply (e.heat.mass.massOperator_isPositive _ measurableSet_ball).smul_of_nonneg
    have hs := distanceSourceRadius_pos e.heat.radius_pos (e.heat.shift + i)
    positivity
  have hroom' i y (hy : y ∈ s i) : dist (centers i y).val q ≤
      e.heat.radius / (2 : ℝ) ^ (e.heat.shift + i + 15) := by
    have hr : 0 < e.heat.radius / (2 : ℝ) ^ (e.heat.shift + i + 15) := div_pos e.heat.radius_pos (by positivity)
    linarith [hroom i y hy]
  have hsmallC i y (hy : y ∈ s i) (v : Euclidean n) :
      ⟪v, C₀ i y v⟫_ℝ ≤ epsilon * ⟪v, Q i v⟫_ℝ := by
    have h := regular_raw_patch_mass_small hX e hq (centers i y).property
      hzeta hzeta1 hCχ hsmall hnear (e.heat.shift + i) (by omega) (hroom' i y hy) v
    exact h.trans (mul_le_mul_of_nonneg_right (hcoefficient i) ((e.heat.heatAt_isPositive q _).inner_nonneg_right v))
  have herr : (∑ i ∈ Finset.range k, ∑ y ∈ s i,
      ⟪z₀ i y - a₀ i, C₀ i y (z₀ i y - a₀ i)⟫_ℝ) ≤ V * epsilon * H := by
    have h := normalization_mass_errors_sum_le (fun i => (Q i).toContinuousLinearMap) C₀ s
      (fun i y => z₀ i y - a₀ i) hsmallC k
    have he := regular_shifted_inverse_errors_sum_le hX e hq hzeta hnear s centers N hcard
      hroom' henlargement xi k
    dsimp only at he
    rw [← e.heat.frozenAt_norm_sq q k xi] at he
    change _ ≤ V * H at he
    have hm := mul_le_mul_of_nonneg_left he hepsilon
    simp only [ContinuousLinearEquiv.coe_coe] at h
    change epsilon * (∑ i ∈ Finset.range k, ∑ y ∈ s i,
      ⟪z₀ i y - a₀ i, Q i (z₀ i y - a₀ i)⟫_ℝ) ≤ epsilon * (V * H) at hm
    exact (h.trans hm).trans_eq (by ring)
  have hu : (∑ i ∈ Finset.range k, ∑ y ∈ s i, ⟪a₀ i, C₀ i y (a₀ i)⟫_ℝ) ≤ U * H :=
    e.heat.raw_patch_mass_sum_le hq s (fun i y => (centers i y).val) N hcard hroom xi k
  have hcent : H ≤ K₀ * (‖xi‖ ^ 2 + ∑ i ∈ Finset.range k, ⟪a₀ i, N₀ i (a₀ i)⟫_ℝ) := by
    have h := (hcentral q hq xi k).2
    have hm : 0 ≤ ∑ i ∈ Finset.range k,
        ⟪a₀ i, dyadicBochnerMass e.heat.mass n q e.heat.radius (e.heat.shift + i + 17) (a₀ i)⟫_ℝ :=
      Finset.sum_nonneg (fun i _ => (dyadicBochnerMass_isPositive e.heat.mass n q e.heat.radius_pos.le _).inner_nonneg_right _)
    have ht := central_comparison_rescale (sq_nonneg ‖xi‖) hm hT.le hc h
    simpa only [N₀, smul_apply, inner_smul_right, ← Finset.mul_sum] using ht
  have hcover' i : ∃ y ∈ s i, weight i y = 1 ∧ ∀ v, ⟪v, N₀ i v⟫_ℝ ≤ ⟪v, C₀ i y v⟫_ℝ := by
    obtain ⟨y, hy, hw⟩ := hcover i
    refine ⟨y, hy, hw, ?_⟩
    intro v
    simpa only [N₀, smul_apply, inner_smul_right] using
      rawPinchingMass_covers_central e.heat.mass n e.heat.radius_pos (e.heat.shift + i) (hroom i y hy) v
  have hh := local_mass_cumulative_comparison N₀ C₀ s weight a₀ z₀ hC₀ hweight hcover'
    (sq_nonneg ‖e.heat.frozenAt q k xi‖) hK₀.le k hu herr hcent habsorb
  have hD (i y) : ⟪xi, D i y xi⟫_ℝ = ⟪z₀ i y, C₀ i y (z₀ i y)⟫_ℝ := by
    change ⟪xi, frozenConjugate (R i y) (C₀ i y) xi⟫_ℝ = _
    exact inner_frozenConjugate _ _ _ _
  simp_rw [hD]
  have hmass0 : 0 ≤ ∑ i ∈ Finset.range k, ⟪a₀ i,
      dyadicBochnerMass e.heat.mass n q e.heat.radius (e.heat.shift + i + 17) (a₀ i)⟫_ℝ :=
    Finset.sum_nonneg (fun i _ => (dyadicBochnerMass_isPositive e.heat.mass n q e.heat.radius_pos.le _).inner_nonneg_right _)
  have hnorm : ‖xi‖ ^ 2 ≤ e.heat.lowerConstant * H := by
    have hl := (hcentral q hq xi k).1
    change ‖xi‖ ^ 2 + _ ≤ e.heat.lowerConstant * H at hl
    linarith only [hl, hmass0]
  have hprincipal : 0 ≤ ∑ i ∈ Finset.range k, ∑ y ∈ s i, weight i y * ⟪z₀ i y, C₀ i y (z₀ i y)⟫_ℝ :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun y hy => mul_nonneg (hweight i y hy) ((hC₀ i y hy).inner_nonneg_right _)))
  have hscale : e.heat.lowerConstant + 2 * (U + V * epsilon) ≤ Theta := by
    have h := mul_le_mul_of_nonneg_left hepsilon1 hV
    dsimp only [Theta]
    nlinarith only [h, hK₀]
  constructor
  · have hb := hh.1
    have hc := mul_le_mul_of_nonneg_right hscale (sq_nonneg ‖e.heat.frozenAt q k xi‖)
    change _ ≤ Theta * H
    nlinarith only [hb, hc, hnorm]
  · have h2 : 2 * K₀ ≤ Theta := by dsimp only [Theta]; linarith [e.heat.lowerConstant_pos]
    have h4 : 4 * K₀ ≤ Theta := by dsimp only [Theta]; linarith [e.heat.lowerConstant_pos]
    have h := add_le_add (mul_le_mul_of_nonneg_right h2 (sq_nonneg ‖xi‖))
      (mul_le_mul_of_nonneg_right h4 hprincipal)
    exact hh.2.trans (by convert h using 1; ring)

end RegularPointCoordinates

end

end OAI
