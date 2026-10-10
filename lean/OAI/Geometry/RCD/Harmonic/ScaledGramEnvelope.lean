import OAI.Geometry.RCD.Coordinates.CoordinateHeatInput
import OAI.Geometry.RCD.Harmonic.GramSourceEstimate
import OAI.Geometry.RCD.Harmonic.HarmonicEndpointBound
import OAI.Geometry.RCD.Harmonic.HarmonicCurvatureBounds
import OAI.Geometry.RCD.Sobolev.ScaledCutoffIntegral
import OAI.Geometry.RCD.Metric.LongTimeMassSum
import OAI.Geometry.RCD.Sobolev.DyadicScalarBackground

namespace OAI

/-! # A radius-independent bound for the actual mean/heat discrepancy -/

open Set Metric MeasureTheory
open scoped InnerProductSpace NNReal ENNReal BoundedContinuousFunction

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [μ.Regular] [IsLocallyFiniteMeasure μ] (hQ : QuadraticCheegerEnergy μ)
  {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel μ hQ ker)

include hk in
/-- The comparison constant is chosen before the physical radius and
harmonic data, using normalized curvature, gradient and source bounds. -/
theorem exists_scaled_actual_gram_envelope_bound (m : ℕ)
    (hg : HasCoordinateHeatBounds μ ker) (hdiff : HasGaussianHeatDifferenceBounds μ ker)
    {A V W c B D Lambda : ℝ} (hA : 0 ≤ A) (hV : 0 < V) (hW : 0 ≤ W)
    (hc : 0 < c) (hB : 0 ≤ B) (hD : 0 ≤ D) (hLambda : 0 ≤ Lambda) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ) (hR : 0 < R), R ≤ 1 →
      ∀ (U : Euclidean (m + 2) →L[ℝ] SobolevSpace μ hQ)
        (M : PositiveBilinearMeasure X (Euclidean (m + 2)))
        (κ : ℝ) (p : X) (r₀ : ℝ) (L : ℝ≥0)
        (G : ∀ v, LocalHarmonicEnergy μ hQ U M κ p r₀ L v)
        (ρ C₀ : ℝ) (χ : GoodLaplacianCutoff μ hQ p ρ C₀),
      0 < ρ → ρ < r₀ → (L : ℝ) ^ 2 ≤ B → |κ| * R ^ 2 ≤ 1 →
      (∀ w : Euclidean (m + 2), ‖w‖ ≤ 2 → R ^ 2 *
        (∫ z, |cutoffSourceDensity μ hQ (G w).energy χ.sobolev χ.laplacian z| ∂μ) ≤ D * R ^ (m + 2)) →
      ∀ lambda : ℝ, |lambda| * R ^ 2 ≤ Lambda → ∀ i : ℕ, 1 ≤ i → ∀ x q : X,
      μ (ball q (R / 2 ^ i)) ≠ ∞ →
      V * (R / 2 ^ i) ^ (m + 2) ≤ μ.real (ball q (R / 2 ^ i)) →
      dist x q ≤ A * (R / 2 ^ i) →
      (∀ j, μ.real (ball x (R / 2 ^ j)) ≤ W * (R / 2 ^ j) ^ (m + 2)) →
      (∀ t, 0 < t → t ≤ R ^ 2 → ∀ z ∈ ball x R,
        V * (Real.sqrt t) ^ (m + 2) ≤ μ.real (ball z (Real.sqrt t))) →
      closedBall p (2 * ρ) ⊆ ball x R →
      (∀ z ∉ ball x R, χ.weight z = 0) →
      (∀ z, ρ ≤ dist p z → dist p z ≤ 2 * ρ → c * R ≤ dist x z) →
      (∀ z ∈ ball q (R / 2 ^ i), χ.weight z = 1) →
      ∀ v : Euclidean (m + 2),
      |⟪v, (sobolevMeanGram μ hQ U (ball q (R / 2 ^ i)) measurableSet_ball -
        cutoffHeatGram μ hQ hk χ.weight.continuous (χ.hasCompactSupport μ hQ)
          U (sq_pos_of_pos (div_pos hR (pow_pos (by norm_num : (0 : ℝ) < 2) i))) x lambda) v⟫_ℝ| ≤
        C * ⟪v, dyadicBochnerEnvelope M (m + 2) x R i v⟫_ℝ := by
  obtain ⟨Ce, hCe, he⟩ := exists_harmonic_endpoint_bound (E := Euclidean (m + 2)) μ hQ hk hg hdiff (m + 2) hA hV hW
  obtain ⟨Cs, hCs, hs⟩ := exists_short_average_mass_integral_bound μ hQ hk hg m hA hV
  obtain ⟨Cl, hCl, hl⟩ := exists_long_time_mass_sum_bound μ hQ hk hg hdiff m hA hV
  obtain ⟨Cc, hCc, hcurvature⟩ := exists_harmonic_curvature_integral_bound (E := Euclidean (m + 2)) μ hQ hk hg hdiff (m + 2) hA hV hW
  obtain ⟨Cx, hCx, hx⟩ := exists_scaled_cutoff_integral_bound μ hQ hk (m + 2)
    hg hdiff hA hV hc hD
  let C := Ce * B + Lambda + 2 * (Cs + Cl) + 4 * Cc * B + 2 * Cx
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro R hR hR1 U M κ p r₀ L G ρ C₀ χ hρ hρr hL hκ hsourceL1 lambda hlambda
    i hi x q hfinite hvolume hcenter hupper hsource hcontain hzero hsep hone v
  let s := R / (2 : ℝ) ^ i
  have hspos : 0 < s := div_pos hR (by positivity)
  have hsR : s ≤ R := div_le_self hR.le (one_le_pow₀ (by norm_num))
  have hsRhalf : s ≤ R / 2 := by
    have hp : (2 : ℝ) ≤ 2 ^ i := by simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hi
    exact div_le_div_of_nonneg_left hR.le (by norm_num) hp
  have hsq : s ^ 2 ≤ R ^ 2 := (sq_le_sq₀ hspos.le hR.le).mpr hsR
  have hpos : 0 < μ.real (ball q s) := (mul_pos hV (pow_pos hspos (m + 2))).trans_le hvolume
  have hχΩ : tsupport (χ.weight : X → ℝ) ⊆ ball p (2 * r₀) := by
    intro z hz
    have hd := χ.tsupport_subset μ hQ hz
    rw [mem_closedBall] at hd
    exact lt_of_le_of_lt hd (by linarith)
  have hsupp : ∀ z, χ.weight z ≠ 0 → z ∈ ball x R := by
    intro z hz
    by_contra hn
    exact hz (hzero z hn)
  have hterm := he R s x q hR hR1 hspos hsRhalf hfinite hpos hcenter
    (by simpa only [pow_zero, div_one] using hupper 0)
    (by simpa only [Real.sqrt_sq hR.le] using hsource (R ^ 2) (sq_pos_of_pos hR) le_rfl)
    U M κ p r₀ L v (G v) χ.weight χ.bounds hχΩ hzero χ.sobolev χ.representative
  have hshort := hs M R hR hR1 x χ.weight (χ.hasCompactSupport μ hQ) χ.bounds hzero i q
    hfinite hvolume hcenter (fun t ht htR z hz => hsource t ht (htR.trans hsq) z (hsupp z hz)) v
  have hlong := hl M R hR hR1 x χ.weight (χ.hasCompactSupport μ hQ) χ.bounds hzero i q
    hfinite hpos hcenter (fun t ht htR z hz => hsource t ht htR z (hsupp z hz)) v
  have hcurv := hcurvature R hR hR1 i x q hfinite hvolume hcenter hupper hsource
    U M κ p r₀ L v (G v) χ.weight χ.bounds hχΩ hzero χ.sobolev χ.representative
  have herr := (hx R hR hR1 U M κ r₀ p L G ρ C₀ χ hρ hρr hsourceL1 s x q hspos hsR hfinite hvolume hcenter hsep
    (fun t ht htR z _ hz => hsource t ht htR z
      (hcontain (by simpa only [mem_closedBall, dist_comm] using hz))) v).2.2
  have hmain := (G v).mean_sub_heat_norm_le μ hQ hk χ hρ hρr
    (ball q s) measurableSet_ball isBounded_ball hone (sq_pos_of_pos hspos) hsq x lambda
  dsimp only at hmain
  have hb := dyadic_scalar_background_bounds M (m + 2) x hR hR1 i v
  have he' := mul_le_mul_of_nonneg_left hb.1 (by positivity : 0 ≤ Ce * (L : ℝ) ^ 2)
  have hregBound := mul_le_mul_of_nonneg_left hb.2.1 (abs_nonneg lambda)
  have hc' := mul_le_mul_of_nonneg_left hb.2.2.1
    (by positivity : 0 ≤ 2 * |κ| * Cc * (L : ℝ) ^ 2)
  have hrelative : ((s / R) ^ 2 + s / R) * ‖v‖ ^ 2 ≤
      2 * ⟪v, dyadicBochnerEnvelope M (m + 2) x R i v⟫_ℝ := by
    have hsr : 0 ≤ s / R := by positivity
    have hsr1 : s / R ≤ 1 := (div_le_one hR).mpr hsR
    have hsqrel : (s / R) ^ 2 ≤ s / R := by nlinarith
    have hh := mul_le_mul_of_nonneg_right hsqrel (sq_nonneg ‖v‖)
    have hbFirst : (s / R) * ‖v‖ ^ 2 ≤
        ⟪v, dyadicBochnerEnvelope M (m + 2) x R i v⟫_ℝ := hb.1
    nlinarith only [hbFirst, hh]
  have hx' := mul_le_mul_of_nonneg_left hrelative hCx.le
  have hcurv' := mul_le_mul_of_nonneg_left hcurv (by positivity : 0 ≤ 2 * |κ|)
  rw [abs_mul, abs_of_nonneg (sq_nonneg s)] at hmain
  have hraw : |⟪v, (sobolevMeanGram μ hQ U (ball q s) measurableSet_ball -
      cutoffHeatGram μ hQ hk χ.weight.continuous (χ.hasCompactSupport μ hQ)
        U (sq_pos_of_pos hspos) x lambda) v⟫_ℝ| ≤
      (Ce * (L : ℝ) ^ 2 + |lambda| * R ^ 2 + 2 * (Cs + Cl) +
        4 * |κ| * Cc * (L : ℝ) ^ 2 * R ^ 2 + 2 * Cx) *
          ⟪v, dyadicBochnerEnvelope M (m + 2) x R i v⟫_ℝ := by
    dsimp only [s] at *
    linear_combination hmain + hterm + 2 * hshort + 2 * hlong + hcurv' + herr +
      he' + hregBound + hc' + hx'
  apply hraw.trans
  apply mul_le_mul_of_nonneg_right _
    ((dyadicBochnerEnvelope_isPositive M (m + 2) x hR.le i).inner_nonneg_right v)
  have hgrad := mul_le_mul_of_nonneg_left hL hCe.le
  have hcurvatureCoeff : 4 * |κ| * Cc * (L : ℝ) ^ 2 * R ^ 2 ≤ 4 * Cc * B := by
    have h := mul_le_mul hκ hL (sq_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    have hh := mul_le_mul_of_nonneg_left h (show 0 ≤ 4 * Cc by positivity)
    nlinarith only [hh]
  dsimp only [C]
  linarith

end RegularPointCoordinates

end

end OAI
