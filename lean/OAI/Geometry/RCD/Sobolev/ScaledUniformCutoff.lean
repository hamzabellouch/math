import OAI.Geometry.RCD.Coordinates.CoordinateHeatInput
import OAI.Geometry.RCD.Heat.ScaledGaussianTail
import OAI.Geometry.RCD.Coordinates.UniformPolarizedError
import OAI.Geometry.RCD.Heat.HeatRegimeBridges

namespace OAI

/-! # A cutoff starting index chosen before the neighborhood radius -/

open Set Metric MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)
  {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel μ hQ ker)

include hk in
/-- A scale-normalized L1 source bound gives a uniform dyadic cutoff index.
The source bound is supplied by `harmonic_cutoff_scaled_L1` for the actual
harmonic coordinates, using the already stated local calculus. -/
theorem exists_scaled_cutoff_error_index (n : ℕ) (hg : HasCoordinateHeatBounds μ ker)
    {A V : ℝ} (hA : 0 ≤ A) (hV : 0 < V) :
    ∃ J : ℕ, ∀ (R : ℝ) (_hR : 0 < R), R ≤ 1 → ∀ (p : X) (r κ C : ℝ) (L : ℝ≥0)
      (U : Euclidean n →L[ℝ] SobolevSpace μ hQ)
      (M : PositiveBilinearMeasure X (Euclidean n))
      (G : ∀ v, LocalHarmonicEnergy μ hQ U M κ p r L v)
      (χ : GoodLaplacianCutoff μ hQ p (3 * R / 8) C),
      (∀ v : Euclidean n, ‖v‖ ≤ 2 →
        R ^ 2 * (∫ z, |cutoffSourceDensity μ hQ (G v).energy χ.sobolev χ.laplacian z| ∂μ) ≤
          A * R ^ n) →
      (∀ y, 3 * R / 8 ≤ dist p y → dist p y ≤ 3 * R / 4 →
        ∀ s, 0 < s → s ≤ R → V * s ^ n ≤ μ.real (ball y s)) →
      ∀ q ∈ ball p (R / 32), ∀ i, J ≤ i →
      ∀ t ∈ Icc ((R / 2 ^ i) ^ 2 / 4) ((R / 2 ^ i) ^ 2),
        ‖harmonicHeatError μ hQ (k := ker) G χ t q‖ ≤ (R ^ 2)⁻¹ := by
  let P := (n : ℝ) ^ 2 * (3 / 2)
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  let eta := 1 / (P + 1)
  have heta : 0 < eta := by dsimp only [eta]; positivity
  obtain ⟨δ, hδ, hδ1, htail⟩ := hg.scaled_off_diagonal_small μ ker hk.nonneg n
    (by norm_num : (0 : ℝ) < 1 / 8) hV (div_pos heta (by positivity : 0 < A + 1))
  obtain ⟨J, hJ⟩ := eventual_dyadic_time_blocks zero_lt_one hδ
  refine ⟨J, ?_⟩
  intro R hR hR1 p r κ C L U M G χ hsource hvol q hq i hi t ht
  have hrpow : 0 < R ^ n := pow_pos hR _
  have hR2 : 0 < R ^ 2 := sq_pos_of_pos hR
  have ht0 : 0 < t := (div_pos (sq_pos_of_pos (div_pos hR (by positivity)))
    (by norm_num : (0 : ℝ) < 4)).trans_le ht.1
  have hunit := (hJ i hi ((1 / (2 : ℝ) ^ i) ^ 2)
    ⟨by nlinarith [sq_nonneg (1 / (2 : ℝ) ^ i)], le_rfl⟩).2
  have httail : t < δ * R ^ 2 := by
    have hm := mul_lt_mul_of_pos_left hunit hR2
    have heq : R ^ 2 * (1 / (2 : ℝ) ^ i) ^ 2 = (R / (2 : ℝ) ^ i) ^ 2 := by ring
    rw [heq] at hm
    exact ht.2.trans_lt (by simpa only [mul_comm] using hm)
  have htR : t ≤ R ^ 2 := httail.le.trans (mul_le_of_le_one_left hR2.le hδ1)
  have hroot : Real.sqrt t ≤ R := by
    nlinarith [Real.sq_sqrt ht0.le, Real.sqrt_nonneg t]
  have hscalar (v : Euclidean n) (hv : ‖v‖ ≤ 2) :
      |∫ z, ker t q z * cutoffSourceDensity μ hQ (G v).energy χ.sobolev χ.laplacian z ∂μ| ≤
        eta / R ^ 2 := by
    have hb := χ.heat_error_le μ hQ (G v).energy (ker t q)
      (div_nonneg (div_pos heta (by positivity : 0 < A + 1)).le hrpow.le) (by
        intro y hy hy'
        have hpy : dist p y ≤ 3 * R / 4 := by linarith
        have hsep : (1 / 8 : ℝ) * R ≤ dist q y := by
          have hqp : dist p q < R / 32 := by simpa only [mem_ball, dist_comm] using hq
          linarith [dist_triangle p q y]
        have htail' := htail R hR hR1 t ht0 httail q y hsep
          (hvol y hy hpy (Real.sqrt t) (Real.sqrt_pos.mpr ht0) hroot)
        exact (le_div_iff₀ hrpow).mpr (by simpa only [mul_comm] using htail'))
    have hs := hsource v hv
    have hI : (∫ z, |cutoffSourceDensity μ hQ (G v).energy χ.sobolev χ.laplacian z| ∂μ) ≤
        A * R ^ n / R ^ 2 := (le_div_iff₀ hR2).mpr (by simpa only [mul_comm] using hs)
    have hm := mul_le_mul_of_nonneg_left hI
      (div_nonneg (div_pos heta (by positivity : 0 < A + 1)).le hrpow.le)
    apply hb.trans (hm.trans ?_)
    have heq : ((eta / (A + 1)) / R ^ n) * (A * R ^ n / R ^ 2) =
        (eta / R ^ 2) * (A / (A + 1)) := by field_simp
    rw [heq]
    apply mul_le_of_le_one_right (div_pos heta hR2).le
    exact (div_le_one (by positivity : 0 < A + 1)).mpr (by linarith)
  have hnorm := polarizedDerivative_norm_le
    (fun v => ∫ z, ker t q z * cutoffSourceDensity μ hQ (G v).energy χ.sobolev χ.laplacian z ∂μ)
    (div_pos heta hR2).le
    (fun j => hscalar (EuclideanSpace.single j 1) (by simp only [PiLp.norm_single, norm_one]; norm_num))
    (fun j k => hscalar (EuclideanSpace.single j 1 + EuclideanSpace.single k 1)
      ((norm_add_le _ _).trans (by simp only [PiLp.norm_single, norm_one]; norm_num)))
  change ‖polarizedDerivative _‖ ≤ _
  apply hnorm.trans
  have hPe : P * eta ≤ 1 := by
    dsimp only [eta]
    rw [mul_one_div]
    exact (div_le_one (by positivity : 0 < P + 1)).mpr (by linarith)
  have hm := mul_le_mul_of_nonneg_right hPe (inv_pos.mpr hR2).le
  simpa only [P, div_eq_mul_inv, mul_assoc, one_mul] using hm

end RegularPointCoordinates

end

end OAI
