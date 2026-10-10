import OAI.Geometry.RCD.Sobolev.PoissonSourceLocalization
import OAI.Geometry.RCD.Sobolev.PoissonCommonRegion

namespace OAI

/-! # Full shifted mass of an actual dyadic Poisson replacement -/

open Set Metric MeasureTheory
open scoped NNReal ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (hQ : QuadraticCheegerEnergy μ)

/-- The energy-density error is valid on each common interior ball, with
the actual squared-distance datum on its right side. -/
theorem DyadicDistanceReplacements.local_density_error
    {n : ℕ} {κ r0 B J C : ℝ} {p : X}
    {S : DyadicDistanceSources μ hQ n κ p r0}
    (T : DyadicDistanceReplacements μ hQ S B J C) (i : ℕ)
    (z : X) {R : ℝ} (hroom : R + dist z p ≤ distanceSourceRadius r0 i) :
    let s := distanceSourceRadius r0 i
    let q := positiveSquaredDistance μ hQ
      (by have := distanceSourceRadius_pos S.radius_pos i; positivity : 0 ≤ 4 * s) (T.cutoff i)
    (∫ x in ball z R,
      |(1 / 2 : ℝ) * localGamma μ hQ (T.replacement i) (T.replacement i) x -
        SobolevSpace.toLp μ hQ q x| ∂μ) ≤
      (J + B / 2) * s ^ 2 * (S.source i).real (ball p s) := by
  dsimp only
  let s := distanceSourceRadius r0 i
  have hs : 0 < s := distanceSourceRadius_pos S.radius_pos i
  let q := positiveSquaredDistance μ hQ (by positivity : 0 ≤ 4 * s) (T.cutoff i)
  have hsub : ball z R ⊆ ball p s := ball_subset_ball' hroom
  have heq := positiveSquaredDistance_energy_value μ hQ
    (by positivity : 0 ≤ 4 * s) (T.cutoff i) (S.eikonal i)
  have heq' := ae_restrict_of_ae_restrict_of_subset
    (hsub.trans (ball_subset_ball (by linarith : s ≤ 4 * s))) heq
  have hi := (((localGamma_memL1 μ hQ (T.replacement i) (T.replacement i)).const_mul
    (1 / 2 : ℝ)).sub ((localGamma_memL1 μ hQ q q).const_mul (1 / 2 : ℝ))).abs
  calc
    _ = ∫ x in ball z R,
        |(1 / 2 : ℝ) * localGamma μ hQ (T.replacement i) (T.replacement i) x -
          (1 / 2 : ℝ) * localGamma μ hQ q q x| ∂μ := by
      apply integral_congr_ae
      filter_upwards [heq'] with x hx
      rw [hx]
    _ ≤ ∫ x in ball p s,
        |(1 / 2 : ℝ) * localGamma μ hQ (T.replacement i) (T.replacement i) x -
          (1 / 2 : ℝ) * localGamma μ hQ q q x| ∂μ :=
      setIntegral_mono_set hi.integrableOn (Filter.Eventually.of_forall fun _ => abs_nonneg _)
        (Filter.Eventually.of_forall hsub)
    _ ≤ _ := T.density_error i

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The same global Poisson energy error controls every local testing
ball. It concerns the actual datum selected by the replacement family. -/
theorem DyadicDistanceReplacements.local_energy_error
    {n : ℕ} {κ r0 B J C : ℝ} {p : X}
    {S : DyadicDistanceSources μ hQ n κ p r0}
    (T : DyadicDistanceReplacements μ hQ S B J C) (i : ℕ) (Ω : Set X) :
    let s := distanceSourceRadius r0 i
    let q := positiveSquaredDistance μ hQ
      (by have := distanceSourceRadius_pos S.radius_pos i; positivity : 0 ≤ 4 * s) (T.cutoff i)
    (∫ x in Ω, localGamma μ hQ (q - T.replacement i) (q - T.replacement i) x ∂μ) ≤
      (S.source i).real (ball p s) * (B * s ^ 2) := by
  dsimp only
  rw [integral_congr_ae (ae_restrict_of_ae (localGamma_self μ hQ _))]
  exact (setIntegral_le_integral
    ((localGamma_memL1 μ hQ _ _).congr (localGamma_self μ hQ _))
    (Filter.Eventually.of_forall fun _ => sq_nonneg _)).trans (T.energy_error i)

/-- The cutoff calculation for an actual replacement retains the full
shifted measure. Both its source and curvature errors have the correct
length units; no mass estimate is assumed. -/
theorem DyadicDistanceReplacements.shifted_mass_le
    {n : ℕ} {κ r0 B J C A Cχ : ℝ} {p z : X}
    {S : DyadicDistanceSources μ hQ n κ p r0}
    (T : DyadicDistanceReplacements μ hQ S B J C) (i : ℕ)
    (hκ : 0 ≤ κ) (hCχ : 0 ≤ Cχ)
    (hroom : dist z p ≤ distanceSourceRadius r0 i / 4)
    {U : E →L[ℝ] SobolevSpace μ hQ} {M : PositiveBilinearMeasure X E}
    {L : ℝ≥0} {v : E} (ell : E →ₗ[ℝ] ℝ)
    [IsFiniteMeasure (μ.restrict (ball z (2 * (distanceSourceRadius r0 i / 32))))]
    (G : LocalHarmonicEnergy μ hQ U M κ z (distanceSourceRadius r0 i / 32) L v)
    (hv : U v = T.replacement i)
    (hell : ell v = (n : ℝ) + κ * (4 * distanceSourceRadius r0 i) ^ 2)
    (hshift : ShiftedBochnerLowerBound M
      (μ.restrict (ball z (2 * (distanceSourceRadius r0 i / 32)))) ell n)
    (χ : GoodLaplacianCutoff μ hQ z (distanceSourceRadius r0 i / 64) Cχ)
    (hgrad : ∀ᵐ x ∂μ.restrict (ball z (2 * (distanceSourceRadius r0 i / 32))),
      localGamma μ hQ (T.replacement i) (T.replacement i) x ≤
        A ^ 2 * (distanceSourceRadius r0 i) ^ 2) :
    let s := distanceSourceRadius r0 i
    ((shiftedBochnerMeasure M (μ.restrict (ball z (2 * (s / 32)))) ell n hshift).measure
      (WithLp.toLp 2 (v, (1 : ℝ)))).real (ball z (s / 64)) ≤
      4096 * Cχ * (J + B / 2) * (S.source i).real (ball p s) +
        κ * A ^ 2 * s ^ 2 * μ.real (ball p s) := by
  let s := distanceSourceRadius r0 i
  have hs : 0 < s := distanceSourceRadius_pos S.radius_pos i
  have hsub : ball z (2 * (s / 32)) ⊆ ball p s :=
    ball_subset_ball' (by change dist z p ≤ s / 4 at hroom; linarith)
  have hfin : μ (ball p s) ≠ ∞ :=
    measure_ne_top_of_subset ball_subset_closedBall (isCompact_closedBall p s).measure_ne_top
  have hsmallfin : μ (ball z (2 * (s / 32))) ≠ ∞ := measure_ne_top_of_subset hsub hfin
  let _ := S.finite i
  let q := positiveSquaredDistance μ hQ (by positivity : 0 ≤ 4 * s) (T.cutoff i)
  have hsource := positiveSquaredDistance_source μ hQ (by positivity : 0 ≤ 4 * s)
    (T.cutoff i) (by linarith : s ≤ 4 * s) (S.source i) (S.defect i)
  have hsource' := positive_defect_mono μ hQ hsub q (S.source i)
    ((n : ℝ) + κ * (4 * s) ^ 2) hsource
  have hsupp : tsupport (χ.weight : X → ℝ) ⊆ ball z (2 * (s / 32)) :=
    (χ.tsupport_subset μ hQ).trans (closedBall_subset_ball (by linarith))
  have hzero : ∀ᵐ x ∂μ, x ∉ ball z (2 * (s / 32)) → χ.laplacian x = 0 := by
    filter_upwards [χ.laplacian_locality] with x hx hn
    apply hx
    right
    have hd : 2 * (s / 32) ≤ dist z x := by
      simpa only [mem_ball, not_lt, dist_comm] using hn
    linarith
  have herr := T.local_density_error μ hQ i z
    (by change dist z p ≤ s / 4 at hroom; linarith : 2 * (s / 32) + dist z p ≤ s)
  have hmass := shifted_poisson_mass_of_positive_defect μ hQ G ell (n : ℝ) hshift
    q (S.source i) (by simpa only [hell] using hsource') χ.weight χ.bounds χ.lipschitz
    (χ.hasCompactSupport μ hQ) hsupp χ.sobolev χ.representative χ.laplacian
    χ.weak_laplacian hzero (ball z (s / 64)) measurableSet_ball χ.one
    (div_nonneg hCχ (sq_nonneg (s / 64))) hκ
    (by rw [hell]; have := mul_nonneg hκ (sq_nonneg (4 * s)); linarith)
    (ae_restrict_of_ae χ.laplacian_bound) (by simpa only [hv] using herr)
  have hcurv : (∫ x in ball z (2 * (s / 32)), localGamma μ hQ (U v) (U v) x ∂μ) ≤
      A ^ 2 * s ^ 2 * μ.real (ball p s) := by
    calc
      _ ≤ ∫ _x in ball z (2 * (s / 32)), A ^ 2 * s ^ 2 ∂μ := by
        apply integral_mono_ae (localGamma_memL1 μ hQ (U v) (U v)).integrableOn
          (integrableOn_const hsmallfin)
        filter_upwards [hgrad] with x hx
        change localGamma μ hQ (U v) (U v) x ≤ A ^ 2 * s ^ 2
        simpa only [hv] using hx
      _ = A ^ 2 * s ^ 2 * μ.real (ball z (2 * (s / 32))) := by
        rw [setIntegral_const, smul_eq_mul, mul_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_left (measureReal_mono hsub hfin) (by positivity)
  have herror_units : Cχ / (s / 64) ^ 2 *
      ((J + B / 2) * s ^ 2 * (S.source i).real (ball p s)) =
      4096 * Cχ * (J + B / 2) * (S.source i).real (ball p s) := by
    field_simp [hs.ne']
    ring
  exact hmass.trans (by rw [herror_units]; nlinarith [mul_le_mul_of_nonneg_left hcurv hκ])

end RegularPointCoordinates

end

end OAI
