import OAI.Geometry.RCD.Sobolev.ActualPoissonMass
import OAI.Geometry.RCD.Metric.PositiveDistanceLocality
import OAI.Geometry.RCD.Harmonic.RadialDerivativeError
import OAI.Analysis.RCDHeat.HopfTransport

namespace OAI

/-! # The actual radial error for the transport estimate -/

open Set Metric MeasureTheory
open scoped ENNReal NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (hQ : QuadraticCheegerEnergy μ)

/-- The compact squared-distance datum has the exact inward pairing
on every smaller ball. -/
theorem positiveSquaredDistance_inward_smaller {p : X} {R r C : ℝ}
    (hR : 0 ≤ R) (hrR : r ≤ R) (χ : GoodLaplacianCutoff μ hQ p R C)
    (heik : ∀ᵐ x ∂μ.restrict (ball p R),
      localGamma μ hQ (inwardSobolev μ hQ p R) (inwardSobolev μ hQ p R) x = 1) :
    localGamma μ hQ (positiveSquaredDistance μ hQ hR χ) (inwardSobolev μ hQ p r) =ᵐ[
      μ.restrict (ball p r)] fun x => -dist p x := by
  have heq := localGamma_eq_of_constant_difference μ hQ (ball p r)
    (inwardSobolev μ hQ p R) (inwardSobolev μ hQ p r)
    (inwardSobolev μ hQ p r) (R - r) (inwardSobolev_constant_difference μ hQ p hrR)
  have hs := inwardSobolev_eikonal_mono μ hQ p hrR heik
  have hq := ae_restrict_of_ae_restrict_of_subset (ball_subset_ball hrR)
    (positiveSquaredDistance_gamma μ hQ hR χ (inwardSobolev μ hQ p r))
  filter_upwards [heq, hs, hq] with x hc he hd
  rw [hd, hc, he, mul_one]

/-- The error is an actual square-integrable gradient pairing. Its full
L2 mass is bounded by the same source energy, even across the transport
cutoff. The radial identity is asserted only inside that cutoff. -/
theorem DyadicDistanceReplacements.radial_transport_defect
    {n : ℕ} {κ r0 B J C : ℝ} {p : X}
    {S : DyadicDistanceSources μ hQ n κ p r0}
    (T : DyadicDistanceReplacements μ hQ S B J C) (i : ℕ)
    {R : ℝ} (_hR : 0 < R) (hroom : 3 * R ≤ 4 * distanceSourceRadius r0 i) :
    ∃ g : X → ℝ, MemLp g 2 μ ∧
      (localGamma μ hQ (T.replacement i) (inwardSobolev μ hQ p (3 * R)) =ᵐ[
        μ.restrict (ball p (3 * R))] fun x => g x - dist p x) ∧
      (∫ x in ball p (4 * R), (g x) ^ 2 ∂μ) ≤
        (S.source i).real (ball p (distanceSourceRadius r0 i)) *
          (B * (distanceSourceRadius r0 i) ^ 2) := by
  let s := distanceSourceRadius r0 i
  let q := positiveSquaredDistance μ hQ
    (by have := distanceSourceRadius_pos S.radius_pos i; positivity : 0 ≤ 4 * s) (T.cutoff i)
  let a := inwardSobolev μ hQ p (3 * R)
  let g : X → ℝ := fun x => -localGamma μ hQ (q - T.replacement i) a x
  have hs : 0 < s := distanceSourceRadius_pos S.radius_pos i
  have ha : ∀ᵐ x ∂μ, localGamma μ hQ a a x ≤ 1 := by
    have hl := SobolevSpace.ofLipschitzCompact_minimalSlope_le_lip μ hQ
      (inwardDistance_lipschitz p (3 * R)) (inwardDistance_compact p (3 * R))
    have hn := (Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ hQ a)
    filter_upwards [hl, hn, localGamma_self μ hQ a] with x hl hn he
    change SobolevSpace.minimalSlope μ hQ a x ≤ (1 : ℝ≥0) at hl
    change 0 ≤ SobolevSpace.minimalSlope μ hQ a x at hn
    rw [he]
    norm_num only [NNReal.coe_one] at hl
    nlinarith
  have hg : MemLp g 2 μ := by
    have hmem := localGamma_memLp_two_of_bound μ hQ Set.univ (q - T.replacement i) a
      (ae_restrict_of_ae ha)
    rw [Measure.restrict_univ] at hmem
    simpa only [g, neg_one_mul] using hmem.const_mul (-1)
  have hq := positiveSquaredDistance_inward_smaller μ hQ
    (by positivity : 0 ≤ 4 * s) hroom (T.cutoff i) (S.eikonal i)
  refine ⟨g, hg, ?_, ?_⟩
  · filter_upwards [hq, ae_restrict_of_ae (localGamma_sub_left μ hQ q (T.replacement i) a)]
      with x hq hs
    change localGamma μ hQ (T.replacement i) a x = _
    change localGamma μ hQ q a x = -dist p x at hq
    dsimp only [g]
    linarith
  · have hsq : ∀ᵐ x ∂μ, (g x) ^ 2 ≤ localGamma μ hQ (q - T.replacement i) (q - T.replacement i) x := by
      filter_upwards [localGamma_sq_le μ hQ (q - T.replacement i) a, ha,
        localGamma_self μ hQ (q - T.replacement i)] with x hx ha he
      dsimp only [g]
      rw [neg_sq]
      exact hx.trans (by rw [he]; nlinarith [sq_nonneg (SobolevSpace.minimalSlope μ hQ (q - T.replacement i) x)])
    have hi := integral_mono_ae (hg.restrict (ball p (4 * R))).integrable_sq
      (localGamma_memL1 μ hQ (q - T.replacement i) (q - T.replacement i)).integrableOn
      (ae_restrict_of_ae hsq)
    exact hi.trans (T.local_energy_error μ hQ i (ball p (4 * R)))

end RegularPointCoordinates

end

end OAI
