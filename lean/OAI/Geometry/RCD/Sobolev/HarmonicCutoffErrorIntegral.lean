import OAI.Geometry.RCD.Coordinates.CoordinateHeatInput
import OAI.Geometry.RCD.Sobolev.HarmonicCutoffErrorBounds
import OAI.Geometry.RCD.Heat.HeatBlockIntegrals

namespace OAI

/-! # Time-integrated actual cutoff errors -/

open Set Metric MeasureTheory Filter
open scoped InnerProductSpace NNReal ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [μ.Regular] [IsLocallyFiniteMeasure μ] (hQ : QuadraticCheegerEnergy μ)
  {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel μ hQ ker)
  {n : ℕ} {U : Euclidean n →L[ℝ] SobolevSpace μ hQ}
  {M : PositiveBilinearMeasure X (Euclidean n)} {κ : ℝ} {p : X} {r₀ : ℝ} {L : ℝ≥0}
  (G : ∀ v, LocalHarmonicEnergy μ hQ U M κ p r₀ L v)
  {ρ C₀ : ℝ} (χ : GoodLaplacianCutoff μ hQ p ρ C₀)

include hk in
/-- Both error time integrals exist, and their sum vanishes with the
averaging radius. The uniform constant uses only finitely many source masses. -/
theorem exists_harmonic_cutoff_error_integral_bound (hg : HasCoordinateHeatBounds μ ker)
    (hdiff : HasGaussianHeatDifferenceBounds μ ker) (hρ : 0 < ρ) (hρr : ρ < r₀)
    {A V δ : ℝ} (hA : 0 ≤ A) (hV : 0 < V) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R r : ℝ) (x q : X),
      0 < R → R ≤ 1 → 0 < r → r ≤ R →
      μ (ball q r) ≠ ∞ → V * r ^ n ≤ μ.real (ball q r) → dist x q ≤ A * r →
      (∀ z, ρ ≤ dist p z → dist p z ≤ 2 * ρ → δ ≤ dist x z) →
      (∀ t, 0 < t → t ≤ R ^ 2 → ∀ z, ρ ≤ dist p z → dist p z ≤ 2 * ρ →
        V * (Real.sqrt t) ^ n ≤ μ.real (ball z (Real.sqrt t))) →
      ∀ v : Euclidean n,
      IntervalIntegrable (fun t => ∫ z, kernelAverage μ ker t (ball q r) z *
        cutoffSourceDensity μ hQ (G v).energy χ.sobolev χ.laplacian z ∂μ) volume 0 (r ^ 2) ∧
      IntervalIntegrable (fun t => ∫ z, (kernelAverage μ ker t (ball q r) z - ker t x z) *
        cutoffSourceDensity μ hQ (G v).energy χ.sobolev χ.laplacian z ∂μ) volume (r ^ 2) (R ^ 2) ∧
      |∫ t in (0 : ℝ)..r ^ 2, ∫ z, kernelAverage μ ker t (ball q r) z *
        cutoffSourceDensity μ hQ (G v).energy χ.sobolev χ.laplacian z ∂μ| +
      |∫ t in r ^ 2..R ^ 2, ∫ z, (kernelAverage μ ker t (ball q r) z - ker t x z) *
        cutoffSourceDensity μ hQ (G v).energy χ.sobolev χ.laplacian z ∂μ| ≤
        C * ‖v‖ ^ 2 * (r ^ 2 + r * R ^ 2) := by
  obtain ⟨C, hC, hb⟩ := exists_harmonic_cutoff_error_bound μ hQ hk G χ hg hdiff hρ hρr hA hV hδ
  refine ⟨C, hC, ?_⟩
  intro R r x q hR hR1 hr hrR hfinite hvolume hcenter hsep hsource v
  let d := fun z => cutoffSourceDensity μ hQ (G v).energy χ.sobolev χ.laplacian z
  let f := fun t => ∫ z, kernelAverage μ ker t (ball q r) z * d z ∂μ
  let g := fun t => ∫ z, (kernelAverage μ ker t (ball q r) z - ker t x z) * d z ∂μ
  let B := C * ‖v‖ ^ 2
  have hB : 0 ≤ B := mul_nonneg hC.le (sq_nonneg _)
  have hrr : r ^ 2 ≤ R ^ 2 := (sq_le_sq₀ hr.le hR.le).mpr hrR
  have hR2 : R ^ 2 ≤ 1 := by nlinarith
  have hr1 : r ≤ 1 := hrR.trans hR1
  have hd : Integrable d μ := cutoffSourceDensity_integrable μ hQ _ _ _
  have hz : ∀ᵐ z ∂μ, z ∉ closedBall p (2 * ρ) → d z = 0 :=
    χ.error_zero_off_outerBall μ hQ _
  have hfc : ContinuousOn f (Ioi 0) := average_density_continuousOn_time μ hQ hk
    (ball q r) measurableSet_ball hfinite hd (isCompact_closedBall p (2 * ρ)) hz
  have hgc : ContinuousOn g (Ioi 0) := difference_density_continuousOn_time μ hQ hk
    (ball q r) measurableSet_ball isBounded_ball x hd (isCompact_closedBall p (2 * ρ)) hz
  have hfb (t : ℝ) (ht : 0 < t) (htr : t ≤ r ^ 2) : |f t| ≤ B :=
    (hb r t x q hr hr1 ht (htr.trans (hrr.trans hR2)) hfinite hvolume hcenter hsep
      (hsource t ht (htr.trans hrr)) v).1 htr
  have hgb (t : ℝ) (htr : r ^ 2 ≤ t) (htR : t ≤ R ^ 2) : |g t| ≤ B * r := by
    have ht : 0 < t := (sq_pos_of_pos hr).trans_le htr
    have hh := (hb r t x q hr hr1 ht (htR.trans hR2) hfinite hvolume hcenter hsep
      (hsource t ht htR) v).2 htr
    simpa only [B, g, d, mul_assoc, mul_comm, mul_left_comm] using hh
  have hfi : IntervalIntegrable f volume 0 (r ^ 2) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (sq_nonneg r)]
    apply IntegrableOn.of_bound measure_Ioc_lt_top
      ((hfc.mono (fun _ ht => ht.1)).aestronglyMeasurable measurableSet_Ioc) B
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    simpa only [Real.norm_eq_abs] using hfb t ht.1 ht.2
  have hgi : IntervalIntegrable g volume (r ^ 2) (R ^ 2) :=
    (hgc.mono (fun t ht => (sq_pos_of_pos hr).trans_le ht.1)).intervalIntegrable_of_Icc hrr
  refine ⟨hfi, hgi, ?_⟩
  have hshort : |∫ t in (0 : ℝ)..r ^ 2, f t| ≤ B * r ^ 2 :=
    short_time_integral_norm_le hr (mul_nonneg hB (sq_nonneg r)) (by
      intro t ht htr
      nlinarith only [mul_le_mul_of_nonneg_left (hfb t ht htr) (sq_nonneg r)])
  have hlong : |∫ t in r ^ 2..R ^ 2, g t| ≤ B * r * R ^ 2 := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (C := B * r) (f := g) (by
      intro t ht
      rw [uIoc_of_le hrr] at ht
      simpa only [Real.norm_eq_abs] using hgb t ht.1.le ht.2)
    rw [abs_of_nonneg (sub_nonneg.mpr hrr)] at h
    have hc : 0 ≤ B * r := mul_nonneg hB hr.le
    have hh : B * r * (R ^ 2 - r ^ 2) ≤ B * r * R ^ 2 :=
      mul_le_mul_of_nonneg_left (by linarith [sq_nonneg r]) hc
    exact h.trans hh
  change _ ≤ B * (r ^ 2 + r * R ^ 2)
  change |∫ t in (0 : ℝ)..r ^ 2, f t| + |∫ t in r ^ 2..R ^ 2, g t| ≤ _
  nlinarith only [hshort, hlong]

end RegularPointCoordinates

end

end OAI
