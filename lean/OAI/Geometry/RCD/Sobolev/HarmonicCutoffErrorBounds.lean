import OAI.Geometry.RCD.Coordinates.CoordinateHeatInput
import OAI.Geometry.RCD.Sobolev.AveragedCutoffError
import OAI.Geometry.RCD.Heat.SeparatedSourceBounds

namespace OAI

/-! # Uniform bounds for every direction of the actual annular error -/

open Set Metric MeasureTheory
open scoped InnerProductSpace NNReal ENNReal

noncomputable section
namespace RegularPointCoordinates

private theorem abs_quadratic_le_norm {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (B : E →L[ℝ] E) (v : E) :
    |⟪v, B v⟫_ℝ| ≤ ‖B‖ * ‖v‖ ^ 2 := by
  calc
    _ ≤ ‖v‖ * ‖B v‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖v‖ * (‖B‖ * ‖v‖) := mul_le_mul_of_nonneg_left (B.le_opNorm v) (norm_nonneg _)
    _ = _ := by ring

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [μ.Regular] [IsLocallyFiniteMeasure μ] (hQ : QuadraticCheegerEnergy μ)
  {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel μ hQ ker)
  {n : ℕ} {U : Euclidean n →L[ℝ] SobolevSpace μ hQ}
  {M : PositiveBilinearMeasure X (Euclidean n)} {κ : ℝ} {p : X} {r₀ : ℝ} {L : ℝ≥0}
  (G : ∀ v, LocalHarmonicEnergy μ hQ U M κ p r₀ L v)
  {ρ C₀ : ℝ} (χ : GoodLaplacianCutoff μ hQ p ρ C₀)

include hk in
/-- Finitely many genuine L1 error masses control every direction, uniformly
in the averaging scale and center subject to the stated volume/separation bounds. -/
theorem exists_harmonic_cutoff_error_bound (hg : HasCoordinateHeatBounds μ ker)
    (hdiff : HasGaussianHeatDifferenceBounds μ ker) (hρ : 0 < ρ) (hρr : ρ < r₀)
    {A V δ : ℝ} (hA : 0 ≤ A) (hV : 0 < V) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r t : ℝ) (x q : X),
      0 < r → r ≤ 1 → 0 < t → t ≤ 1 →
      μ (ball q r) ≠ ∞ → V * r ^ n ≤ μ.real (ball q r) → dist x q ≤ A * r →
      (∀ z, ρ ≤ dist p z → dist p z ≤ 2 * ρ → δ ≤ dist x z) →
      (∀ z, ρ ≤ dist p z → dist p z ≤ 2 * ρ →
        V * (Real.sqrt t) ^ n ≤ μ.real (ball z (Real.sqrt t))) →
      ∀ v : Euclidean n,
      (t ≤ r ^ 2 → |∫ z, kernelAverage μ ker t (ball q r) z *
        cutoffSourceDensity μ hQ (G v).energy χ.sobolev χ.laplacian z ∂μ| ≤ C * ‖v‖ ^ 2) ∧
      (r ^ 2 ≤ t → |∫ z, (kernelAverage μ ker t (ball q r) z - ker t x z) *
        cutoffSourceDensity μ hQ (G v).energy χ.sobolev χ.laplacian z ∂μ| ≤ C * r * ‖v‖ ^ 2) := by
  let d := fun v z => cutoffSourceDensity μ hQ (G v).energy χ.sobolev χ.laplacian z
  obtain ⟨Cd, hCd, hd⟩ := exists_polarized_integral_bound μ d
  obtain ⟨Cs, hCs, hs⟩ := exists_separated_short_source_bound μ hQ hk hg n hA hV hδ
  obtain ⟨Cl, hCl, hl⟩ := exists_separated_long_source_bound μ hQ hk hg hdiff n hA hV hδ
  refine ⟨Cd * (Cs + Cl), mul_pos hCd (add_pos hCs hCl), ?_⟩
  intro r t x q hr hr1 ht ht1 hfinite hvolume hcenter hsep hsource v
  let S := {z | ρ ≤ dist p z ∧ dist p z ≤ 2 * ρ}
  have hi (w : Euclidean n) : Integrable (d w) μ := cutoffSourceDensity_integrable μ hQ _ _ _
  have hz (w : Euclidean n) : ∀ᵐ z ∂μ, z ∉ S → d w z = 0 :=
    χ.error_zero_off_annulus μ hQ _
  have hsep' : ∀ z ∈ S, δ ≤ dist x z := fun z hz => hsep z hz.1 hz.2
  have hsource' : ∀ z ∈ S, V * (Real.sqrt t) ^ n ≤ μ.real (ball z (Real.sqrt t)) :=
    fun z hz => hsource z hz.1 hz.2
  have hpos : 0 < μ.real (ball q r) := (mul_pos hV (pow_pos hr n)).trans_le hvolume
  constructor
  · intro htr
    have hop := hd (fun z => kernelAverage μ ker t (ball q r) z) Cs hCs.le
      (fun w => hs r t x q S (d w) hr hr1 ht htr hfinite hvolume hcenter hsep' hsource' (hi w) (hz w))
    rw [← averaged_cutoff_error_energy μ hQ hk G χ hρ hρr ht (ball q r)
      measurableSet_ball isBounded_ball v]
    exact (abs_quadratic_le_norm _ v).trans ((mul_le_mul_of_nonneg_right hop (sq_nonneg ‖v‖)).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hCl.le) hCd.le)
        (sq_nonneg ‖v‖)))
  · intro hrt
    have hop := hd (fun z => kernelAverage μ ker t (ball q r) z - ker t x z) (Cl * r)
      (mul_pos hCl hr).le
      (fun w => hl r t x q S (d w) hr ht ht1 hrt hfinite hpos hcenter hsep' hsource' (hi w) (hz w))
    rw [← difference_cutoff_error_energy μ hQ hk G χ hρ hρr ht (ball q r)
      measurableSet_ball isBounded_ball x v]
    have hcoef : Cd * (Cl * r) ≤ Cd * (Cs + Cl) * r := by
      calc
        _ = (Cd * Cl) * r := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hCs.le) hCd.le) hr.le
    exact (abs_quadratic_le_norm _ v).trans ((mul_le_mul_of_nonneg_right hop (sq_nonneg ‖v‖)).trans
      (mul_le_mul_of_nonneg_right hcoef (sq_nonneg ‖v‖)))

end RegularPointCoordinates

end

end OAI
