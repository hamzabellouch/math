import OAI.Geometry.RCD.Coordinates.CoordinateHeatInput
import OAI.Geometry.RCD.Coordinates.ScaledSeparatedSources
import OAI.Geometry.RCD.Sobolev.AveragedCutoffError

namespace OAI

/-! # Uniform normalized bounds for actual cutoff-source pairings -/

open Set Metric MeasureTheory
open scoped InnerProductSpace NNReal ENNReal

noncomputable section
namespace RegularPointCoordinates

private theorem quadratic_norm_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (B : E →L[ℝ] E) (v : E) : |⟪v, B v⟫_ℝ| ≤ ‖B‖ * ‖v‖ ^ 2 := by
  calc
    _ ≤ ‖v‖ * ‖B v‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖v‖ * (‖B‖ * ‖v‖) := mul_le_mul_of_nonneg_left (B.le_opNorm v) (norm_nonneg _)
    _ = _ := by ring

private theorem polarized_norm_of_tests {n : ℕ} (d : Euclidean n → ℝ) {B : ℝ}
    (hB : 0 ≤ B) (hd : ∀ w, ‖w‖ ≤ 2 → |d w| ≤ B) :
    ‖polarizedDerivative d‖ ≤ (n : ℝ) ^ 2 * (3 / 2 * B) := by
  apply polarizedDerivative_norm_le d hB
  · intro i
    apply hd
    simp only [PiLp.norm_single, norm_one]
    norm_num
  · intro i j
    apply hd
    exact (norm_add_le _ _).trans (by simp only [PiLp.norm_single, norm_one]; norm_num)

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [μ.Regular] [IsLocallyFiniteMeasure μ] (hQ : QuadraticCheegerEnergy μ)
  {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel μ hQ ker)

include hk in
/-- Both scalar pairings have constants fixed before the radius and the
actual harmonic map. The input L1 bound is proved for that map separately. -/
theorem exists_scaled_cutoff_pairing_bound (n : ℕ) (hg : HasCoordinateHeatBounds μ ker)
    (hdiff : HasGaussianHeatDifferenceBounds μ ker)
    {A V c B : ℝ} (hA : 0 ≤ A) (hV : 0 < V) (hc : 0 < c) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ), 0 < R →
      ∀ (U : Euclidean n →L[ℝ] SobolevSpace μ hQ) (M : PositiveBilinearMeasure X (Euclidean n))
        (κ r₀ : ℝ) (p : X) (L : ℝ≥0)
        (G : ∀ v, LocalHarmonicEnergy μ hQ U M κ p r₀ L v)
        (ρ C₀ : ℝ) (χ : GoodLaplacianCutoff μ hQ p ρ C₀),
      0 < ρ → ρ < r₀ →
      (∀ w : Euclidean n, ‖w‖ ≤ 2 → R ^ 2 *
        (∫ z, |cutoffSourceDensity μ hQ (G w).energy χ.sobolev χ.laplacian z| ∂μ) ≤ B * R ^ n) →
      ∀ (r t : ℝ) (x q : X), 0 < r → r ≤ 1 → 0 < t → t ≤ 1 →
      μ (ball q r) ≠ ∞ → V * r ^ n ≤ μ.real (ball q r) → dist x q ≤ A * r →
      (∀ z, ρ ≤ dist p z → dist p z ≤ 2 * ρ → c * R ≤ dist x z) →
      (∀ z, ρ ≤ dist p z → dist p z ≤ 2 * ρ →
        V * (Real.sqrt t) ^ n ≤ μ.real (ball z (Real.sqrt t))) →
      ∀ v : Euclidean n,
      (t ≤ r ^ 2 → |∫ z, kernelAverage μ ker t (ball q r) z *
        cutoffSourceDensity μ hQ (G v).energy χ.sobolev χ.laplacian z ∂μ| ≤
          (C / R ^ 2) * ‖v‖ ^ 2) ∧
      (r ^ 2 ≤ t → |∫ z, (kernelAverage μ ker t (ball q r) z - ker t x z) *
        cutoffSourceDensity μ hQ (G v).energy χ.sobolev χ.laplacian z ∂μ| ≤
          (C * r / R ^ 3) * ‖v‖ ^ 2) := by
  obtain ⟨Cs, hCs, hs⟩ := exists_scaled_short_source_bound μ hQ hk hg n hA hV hc
  obtain ⟨Cl, hCl, hl⟩ := exists_scaled_long_source_bound μ hQ hk hg hdiff n hA hV hc
  let P := (n : ℝ) ^ 2 * (3 / 2)
  let C := 1 + P * (Cs + Cl) * B
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  have hCsC : P * (Cs * B) ≤ C := by
    have hh := mul_nonneg (mul_nonneg hP hCl.le) hB
    dsimp only [C]
    nlinarith only [hh]
  have hClC : P * (Cl * B) ≤ C := by
    have hh := mul_nonneg (mul_nonneg hP hCs.le) hB
    dsimp only [C]
    nlinarith only [hh]
  refine ⟨C, hC, ?_⟩
  intro R hR U M κ r₀ p L G ρ C₀ χ hρ hρr hL1 r t x q hr hr1 ht ht1 hfinite hvolume hcenter hsep hsource v
  let d := fun w z => cutoffSourceDensity μ hQ (G w).energy χ.sobolev χ.laplacian z
  let S := {z | ρ ≤ dist p z ∧ dist p z ≤ 2 * ρ}
  have hi (w : Euclidean n) : Integrable (d w) μ := cutoffSourceDensity_integrable μ hQ _ _ _
  have hz (w : Euclidean n) : ∀ᵐ z ∂μ, z ∉ S → d w z = 0 := χ.error_zero_off_annulus μ hQ _
  have hvol' : ∀ z ∈ S, V * (Real.sqrt t) ^ n ≤ μ.real (ball z (Real.sqrt t)) :=
    fun z hz => hsource z hz.1 hz.2
  have hsep' : ∀ z ∈ S, c * R ≤ dist x z := fun z hz => hsep z hz.1 hz.2
  have hIb (w : Euclidean n) (hw : ‖w‖ ≤ 2) : (∫ z, |d w z| ∂μ) ≤ B * R ^ n / R ^ 2 :=
    (le_div_iff₀ (sq_pos_of_pos hR)).mpr (by simpa only [mul_comm] using hL1 w hw)
  constructor
  · intro htr
    have htest (w : Euclidean n) (hw : ‖w‖ ≤ 2) :
        |∫ z, kernelAverage μ ker t (ball q r) z * d w z ∂μ| ≤ Cs * B / R ^ 2 := by
      have h := hs R r t x q S (d w) hR hr hr1 ht htr hfinite hvolume hcenter hsep' hvol' (hi w) (hz w)
      have hm := mul_le_mul_of_nonneg_left (hIb w hw) (by positivity : 0 ≤ Cs / R ^ n)
      apply h.trans (hm.trans_eq ?_)
      field_simp [hR.ne']
    have hop := polarized_norm_of_tests _ (by positivity) htest
    rw [← averaged_cutoff_error_energy μ hQ hk G χ hρ hρr ht (ball q r)
      measurableSet_ball isBounded_ball v]
    apply (quadratic_norm_bound _ v).trans
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply hop.trans
    have hm := div_le_div_of_nonneg_right hCsC (sq_nonneg R)
    simpa only [P, mul_div_assoc, mul_assoc] using hm
  · intro hrt
    have hpos : 0 < μ.real (ball q r) := (mul_pos hV (pow_pos hr n)).trans_le hvolume
    have htest (w : Euclidean n) (hw : ‖w‖ ≤ 2) :
        |∫ z, (kernelAverage μ ker t (ball q r) z - ker t x z) * d w z ∂μ| ≤ Cl * B * r / R ^ 3 := by
      have h := hl R r t x q S (d w) hR hr ht ht1 hrt hfinite hpos hcenter hsep' hvol' (hi w) (hz w)
      have hm := mul_le_mul_of_nonneg_left (hIb w hw) (by positivity : 0 ≤ Cl * r / R ^ (n + 1))
      apply h.trans (hm.trans_eq ?_)
      rw [pow_succ]
      field_simp [hR.ne']
    have hop := polarized_norm_of_tests _ (by positivity) htest
    rw [← difference_cutoff_error_energy μ hQ hk G χ hρ hρr ht (ball q r)
      measurableSet_ball isBounded_ball x v]
    apply (quadratic_norm_bound _ v).trans
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply hop.trans
    have hm := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hClC hr.le) (by positivity : 0 ≤ (R ^ 3)⁻¹)
    simpa only [P, div_eq_mul_inv, mul_assoc] using hm

end RegularPointCoordinates

end

end OAI
