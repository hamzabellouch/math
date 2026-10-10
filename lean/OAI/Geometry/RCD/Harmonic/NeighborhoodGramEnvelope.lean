import OAI.Geometry.RCD.Coordinates.CoordinateHeatInput
import OAI.Geometry.RCD.Harmonic.ActualGramEnvelope

namespace OAI

/-! # One source-comparison constant throughout the regular neighborhood -/

open Set Metric MeasureTheory Filter
open scoped InnerProductSpace NNReal Topology ENNReal

noncomputable section
namespace RegularPointCoordinates

private theorem volume_half_lower {v omega s : ℝ} {n : ℕ}
    (hw : 0 < omega) (hs : 0 < s) (h : |v / (omega * s ^ n) - 1| ≤ 1 / 2) :
    (omega / 2) * s ^ n ≤ v := by
  have hd : 0 < omega * s ^ n := mul_pos hw (pow_pos hs n)
  have hl := (abs_le.mp h).1
  have hq : (1 / 2 : ℝ) ≤ v / (omega * s ^ n) := by linarith
  have hh := (le_div_iff₀ hd).mp hq
  nlinarith only [hh]

private theorem volume_half_upper {v omega s : ℝ} {n : ℕ}
    (hw : 0 < omega) (hs : 0 < s) (h : |v / (omega * s ^ n) - 1| ≤ 1 / 2) :
    v ≤ (3 / 2 * omega) * s ^ n := by
  have hd : 0 < omega * s ^ n := mul_pos hw (pow_pos hs n)
  have hl := (abs_le.mp h).2
  have hq : v / (omega * s ^ n) ≤ (3 / 2 : ℝ) := by linarith
  have hh := (div_le_iff₀ hd).mp hq
  nlinarith only [hh]

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [μ.Regular] [IsLocallyFiniteMeasure μ] (hQ : QuadraticCheegerEnergy μ)
  {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel μ hQ ker)
  {m : ℕ} {U : Euclidean (m + 2) →L[ℝ] SobolevSpace μ hQ}
  {M : PositiveBilinearMeasure X (Euclidean (m + 2))} {κ : ℝ} {p : X}
  {R omega C₀ : ℝ} {L : ℝ≥0}
  (G : ∀ v, LocalHarmonicEnergy μ hQ U M κ p (4 * R) L v)
  (χ : GoodLaplacianCutoff μ hQ p (3 * R / 8) C₀)

include G in
/-- A single finite comparison constant works at all nearby heat poles
and all sufficiently small testing balls, using the same harmonic data. -/
theorem exists_neighborhood_gram_envelope_bound (hg : HasCoordinateHeatBounds μ ker)
    (hdiff : HasGaussianHeatDifferenceBounds μ ker) (hR : 0 < R) (hR1 : R ≤ 1)
    (homega : 0 < omega)
    (hvolume : ∀ y, dist p y ≤ 16 * R → ∀ s, 0 < s → s ≤ 32 * R →
      |μ.real (ball y s) / (omega * s ^ (m + 2)) - 1| ≤ 1 / 2)
    {A : ℝ} (hA : 0 ≤ A) (lambda : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∃ J : ℕ, ∀ i, J ≤ i → ∀ x ∈ ball p (R / 32),
      ∀ q, dist x q ≤ A * (R / 2 ^ i) → ∀ v : Euclidean (m + 2),
      |⟪v, (sobolevMeanGram μ hQ U (ball q (R / 2 ^ i)) measurableSet_ball -
        cutoffHeatGram μ hQ hk χ.weight.continuous (χ.hasCompactSupport μ hQ)
          U (sq_pos_of_pos (div_pos hR (pow_pos (by norm_num : (0 : ℝ) < 2) i))) x lambda) v⟫_ℝ| ≤
        C * ⟪v, dyadicBochnerEnvelope M (m + 2) x R i v⟫_ℝ := by
  obtain ⟨C, hC, hb⟩ := exists_actual_gram_envelope_bound μ hQ hk G χ hg hdiff
    (by positivity) (by linarith) hA (show 0 < omega / 2 by positivity)
    (show 0 ≤ 3 / 2 * omega by positivity) (show 0 < R / 4 by positivity) hR hR1 lambda
  have hrad : Tendsto (fun i : ℕ => R / (2 : ℝ) ^ i) atTop (𝓝 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).const_mul R
    simpa only [mul_zero, div_eq_mul_inv, one_mul, inv_pow] using h
  obtain ⟨J, hJ⟩ := eventually_atTop.mp (hrad.eventually_lt_const
    (div_pos hR (by positivity : 0 < 8 * (A + 1))))
  refine ⟨C, hC, max 1 J, ?_⟩
  intro i hi x hx q hq v
  have hi1 : 1 ≤ i := (le_max_left _ _).trans hi
  have hiJ : J ≤ i := (le_max_right _ _).trans hi
  let s := R / (2 : ℝ) ^ i
  have hs : 0 < s := div_pos hR (by positivity)
  have hsR : s ≤ R := div_le_self hR.le (one_le_pow₀ (by norm_num))
  have hsmall : (A + 1) * s < R / 8 := by
    have hh := (lt_div_iff₀ (by positivity : 0 < 8 * (A + 1))).mp (hJ i hiJ)
    change s * (8 * (A + 1)) < R at hh
    nlinarith only [hh]
  have hxp : dist x p < R / 32 := hx
  have hpx : dist p x < R / 32 := by rwa [dist_comm]
  have hqnear : dist p q ≤ 16 * R := by
    have ht := dist_triangle p x q
    have has : A * s ≤ (A + 1) * s := by nlinarith [hs.le]
    change dist x q ≤ A * s at hq
    linarith
  refine hb i hi1 x q (isBounded_ball.measure_lt_top.ne)
    (volume_half_lower homega hs (hvolume q hqnear s hs (by linarith))) hq ?_ ?_ ?_ ?_ ?_ ?_ v
  · intro j
    have hs' : 0 < R / (2 : ℝ) ^ j := div_pos hR (by positivity)
    have hsR' : R / (2 : ℝ) ^ j ≤ R := div_le_self hR.le (one_le_pow₀ (by norm_num))
    exact volume_half_upper homega hs' (hvolume x (by linarith) _ hs' (by linarith))
  · intro t ht htR z hz
    have hzp : dist z x < R := hz
    have hpz : dist p z ≤ 16 * R := by linarith [dist_triangle p x z, dist_comm z x]
    have hroot : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
    have hrootR : Real.sqrt t ≤ R := by nlinarith [Real.sq_sqrt ht.le, Real.sqrt_nonneg t]
    exact volume_half_lower homega hroot (hvolume z hpz _ hroot (by linarith))
  · intro z hz
    have hzp : dist z p ≤ 2 * (3 * R / 8) := hz
    change dist z x < R
    linarith [dist_triangle z p x]
  · intro z hz
    apply χ.zero z
    have hzx : R ≤ dist z x := by simpa only [mem_ball, not_lt] using hz
    rw [dist_comm p z]
    linarith [dist_triangle z p x]
  · intro z hz _
    have ht := dist_triangle p x z
    linarith
  · intro z hz
    apply χ.one
    have hzq : dist z q < s := hz
    change dist z p < 3 * R / 8
    have ht := dist_triangle z q x
    have ht' := dist_triangle z x p
    rw [dist_comm q x] at ht
    linarith

end RegularPointCoordinates

end

end OAI
