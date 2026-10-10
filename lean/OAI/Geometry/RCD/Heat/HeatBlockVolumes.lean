import OAI.Geometry.RCD.Coordinates.CoordinateHeatInput
import OAI.Geometry.RCD.Metric.VolumeRegime
import OAI.Geometry.RCD.Heat.UniformDyadicHeatBounds

namespace OAI

/-! # Volume control on all intermediate heat radii in a dyadic block -/

open Set Metric MeasureTheory
open scoped InnerProductSpace NNReal

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]

/-- The common almost-Euclidean volume regime supplies the upper and lower
Gaussian denominators throughout an entire dyadic time block. -/
theorem heat_block_volume_bounds (μ : Measure X) (n : ℕ) (z : X)
    {omega ε D s t : ℝ} (homega : 0 < omega) (hε : ε < 1)
    (hs : 0 < s) (hsD : s ≤ D) (ht : t ∈ Icc (s ^ 2 / 4) (s ^ 2))
    (hvolume : ∀ r, 0 < r → r ≤ D →
      |μ.real (ball z r) / (omega * r ^ n) - 1| ≤ ε) :
    0 < μ.real (ball z (Real.sqrt t)) ∧
      ((1 - ε) * omega / 2 ^ n) * s ^ n ≤ μ.real (ball z (Real.sqrt t)) ∧
      μ.real (ball z (Real.sqrt t)) ≤ ((1 + ε) * omega) * s ^ n := by
  have htpos : 0 < t := (div_pos (sq_pos_of_pos hs) (by norm_num : (0 : ℝ) < 4)).trans_le ht.1
  have hrpos := Real.sqrt_pos.mpr htpos
  have hrs : Real.sqrt t ≤ s := (Real.sqrt_le_iff).mpr ⟨hs.le, ht.2⟩
  have hsr : s / 2 ≤ Real.sqrt t := by
    have hsq := Real.sq_sqrt htpos.le
    nlinarith [Real.sqrt_nonneg t, ht.1]
  have hden : 0 < omega * (Real.sqrt t) ^ n := mul_pos homega (pow_pos hrpos n)
  have hv := abs_le.mp (hvolume _ hrpos (hrs.trans hsD))
  have hlo : (1 - ε) * (omega * (Real.sqrt t) ^ n) ≤ μ.real (ball z (Real.sqrt t)) := by
    apply (le_div_iff₀ hden).mp
    linarith [hv.1]
  have hup : μ.real (ball z (Real.sqrt t)) ≤ (1 + ε) * (omega * (Real.sqrt t) ^ n) := by
    apply (div_le_iff₀ hden).mp
    linarith [hv.2]
  have heps : 0 ≤ ε := le_trans (abs_nonneg _) (hvolume _ hrpos (hrs.trans hsD))
  refine ⟨lt_of_lt_of_le (mul_pos (by linarith) hden) hlo, ?_, ?_⟩
  · calc
      _ = ((1 - ε) * omega) * (s / 2) ^ n := by rw [div_pow]; ring
      _ ≤ ((1 - ε) * omega) * (Real.sqrt t) ^ n :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hsr n) (by positivity)
      _ = (1 - ε) * (omega * (Real.sqrt t) ^ n) := by ring
      _ ≤ _ := hlo
  · calc
      _ ≤ (1 + ε) * (omega * (Real.sqrt t) ^ n) := hup
      _ ≤ (1 + ε) * (omega * s ^ n) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hrpos.le hrs n) homega.le) (by linarith)
      _ = _ := by ring

variable [BorelSpace X] [ProperSpace X] (μ : Measure X) [μ.Regular]
  (hQ : QuadraticCheegerEnergy μ) {ker : ℝ → X → X → ℝ}
  (hk : IsContinuousHeatKernel μ hQ ker)
  {n : ℕ} {U : Euclidean n →L[ℝ] SobolevSpace μ hQ}
  {M : PositiveBilinearMeasure X (Euclidean n)} {κ r : ℝ} {p : X} {L : ℝ≥0}
  (G : ∀ v, LocalHarmonicEnergy μ hQ U M κ p r L v)
  {ρ Ccut : ℝ} (χ : GoodLaplacianCutoff μ hQ p ρ Ccut)

/-- A single almost-Euclidean volume regime supplies all volume hypotheses
of the uniform decrement theorem. -/
theorem dyadic_heat_bounds_of_volume_regime (hg : HasCoordinateHeatBounds μ ker)
    (m : ℕ) (hn : n = m + 2) (hρ : 0 < ρ) (hρr : ρ < r) (hκ : 0 ≤ κ)
    {R omega ε η lambda : ℝ} (hR : 0 < R) (hR1 : R ≤ 1)
    (homega : 0 < omega) (hε : 0 ≤ ε) (hε1 : ε < 1)
    (hη : 0 ≤ η) (hlambda : 0 < lambda)
    (hreg : 2 * κ * (L : ℝ) ^ 2 + η ≤ lambda)
    (hχone : ∀ y ∈ ball p R, (χ.weight : X → ℝ) y = 1)
    (herror : ∀ t, 0 < t → t ≤ R ^ 2 → ‖harmonicHeatError μ hQ (k := ker) G χ t p‖ ≤ η)
    (hvolume : ∀ z, dist z p ≤ 2 * ρ + R → ∀ s, 0 < s → s ≤ R →
      |μ.real (ball z s) / (omega * s ^ n) - 1| ≤ ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ i (v : Euclidean n),
      let d := ⟪v, ((dyadicHeatGram μ hQ hk U χ hR hlambda i : Euclidean n →L[ℝ] Euclidean n) -
        (dyadicHeatGram μ hQ hk U χ hR hlambda (i + 1) : Euclidean n →L[ℝ] Euclidean n)) v⟫_ℝ
      0 ≤ d ∧ ⟪v, dyadicBochnerMass M n p R i v⟫_ℝ ≤ C * d ∧
        d ≤ C * ⟪v, dyadicBochnerEnvelope M n p R i v⟫_ℝ := by
  have hVlo : 0 < (1 - ε) * omega / (2 : ℝ) ^ n := by positivity
  have hVhi : 0 < (1 + ε) * omega := by positivity
  apply uniform_dyadic_heat_bounds μ hQ hk G χ hg m hn hρ hρr hκ hR hR1
    hVlo hVhi hη hlambda hreg hχone herror
  · intro i t ht y hy
    have hs : 0 < R / (2 : ℝ) ^ i := div_pos hR (by positivity)
    have hsR : R / (2 : ℝ) ^ i ≤ R := div_le_self hR.le (one_le_pow₀ (by norm_num))
    have hyp : dist y p ≤ 2 * ρ + R := by
      have hdist : dist y p < R / 2 ^ i := hy
      linarith
    have h := heat_block_volume_bounds μ n y homega hε1 hs hsR ht (hvolume y hyp)
    exact ⟨h.1, h.2.2⟩
  · intro i t ht y hy
    have hs : 0 < R / (2 : ℝ) ^ i := div_pos hR (by positivity)
    have hsR : R / (2 : ℝ) ^ i ≤ R := div_le_self hR.le (one_le_pow₀ (by norm_num))
    have hyp : dist y p ≤ 2 * ρ + R := by
      have hdist : dist y p ≤ 2 * ρ := χ.tsupport_subset μ hQ (subset_tsupport χ.weight hy)
      linarith
    exact (heat_block_volume_bounds μ n y homega hε1 hs hsR ht (hvolume y hyp)).2.1

end RegularPointCoordinates

end OAI
