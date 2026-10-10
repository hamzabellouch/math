import OAI.Geometry.RCD.Heat.HeatBlockVolumes
import OAI.Geometry.RCD.Heat.UniformHeatCumulative

namespace OAI

/-! # Passing a common geometric regime to the cumulative heat estimates -/

open Set Metric MeasureTheory Filter
open scoped Topology InnerProductSpace NNReal

noncomputable section

namespace RegularPointCoordinates

/-- A small-time estimate suffices for all sufficiently fine dyadic blocks.
No control at times comparable to the cutoff radius is requested. -/
theorem eventual_dyadic_time_blocks {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) :
    ∃ J : ℕ, ∀ i, J ≤ i → ∀ t ∈ Icc ((R / 2 ^ i) ^ 2 / 4) ((R / 2 ^ i) ^ 2),
      0 < t ∧ t < δ := by
  have htend : Tendsto (fun i : ℕ => (R / (2 : ℝ) ^ i) ^ 2) atTop (𝓝 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).const_mul R
    have h' := h.pow 2
    simpa only [mul_zero, zero_pow (by decide : 2 ≠ 0), div_eq_mul_inv, one_mul, inv_pow] using h'
  obtain ⟨J, hJ⟩ := eventually_atTop.mp (htend.eventually_lt_const hδ)
  refine ⟨J, ?_⟩
  intro i hi t ht
  have hs : 0 < R / (2 : ℝ) ^ i := div_pos hR (by positivity)
  exact ⟨(div_pos (sq_pos_of_pos hs) (by norm_num : (0 : ℝ) < 4)).trans_le ht.1,
    ht.2.trans_lt (hJ i hi)⟩

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]

/-- One half-error volume neighborhood supplies the fixed denominators
used in all dyadic heat blocks. -/
theorem dyadic_heat_volumes_of_common_regime (μ : Measure X) (n : ℕ)
    (p : X) {R omega : ℝ} (hR : 0 < R) (homega : 0 < omega)
    (hvolume : ∀ y, dist p y ≤ 2 * R → ∀ r, 0 < r → r ≤ R →
      |μ.real (ball y r) / (omega * r ^ n) - 1| ≤ 1 / 2) :
    ∀ i y, dist p y ≤ 2 * R →
      ∀ t ∈ Icc ((R / 2 ^ i) ^ 2 / 4) ((R / 2 ^ i) ^ 2),
        (omega / (2 * (2 : ℝ) ^ n)) * (R / 2 ^ i) ^ n ≤ μ.real (ball y (Real.sqrt t)) ∧
        μ.real (ball y (Real.sqrt t)) ≤ ((3 / 2 : ℝ) * omega) * (R / 2 ^ i) ^ n := by
  intro i y hy t ht
  have hs : 0 < R / (2 : ℝ) ^ i := div_pos hR (by positivity)
  have hsR : R / (2 : ℝ) ^ i ≤ R := div_le_self hR.le (one_le_pow₀ (by norm_num))
  have h := heat_block_volume_bounds μ n y homega (by norm_num : (1 / 2 : ℝ) < 1)
    hs hsR ht (hvolume y hy)
  simpa only [show (1 - (1 / 2 : ℝ)) * omega / 2 ^ n = omega / (2 * 2 ^ n) by ring,
    show (1 + (1 / 2 : ℝ)) * omega = (3 / 2 : ℝ) * omega by ring] using h.2

variable [BorelSpace X] [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

omit [ProperSpace X] in
/-- The bounded representative in the local Bochner construction supplies
the original-frame Gamma bound on every smaller working ball. -/
theorem LocalHarmonicEnergy.gamma_bound_on_smaller_ball {n : ℕ}
    {U : Euclidean n →L[ℝ] SobolevSpace μ hQ}
    {M : PositiveBilinearMeasure X (Euclidean n)} {κ r R : ℝ} {L : ℝ≥0} {p : X}
    (G : ∀ v, LocalHarmonicEnergy μ hQ U M κ p r L v) (hR : R ≤ 2 * r)
    (v : Euclidean n) :
    ∀ᵐ x ∂μ.restrict (ball p R), localGamma μ hQ (U v) (U v) x ≤ (L : ℝ) ^ 2 * ‖v‖ ^ 2 := by
  have hre := ae_restrict_of_ae_restrict_of_subset (ball_subset_ball hR) (G v).representative
  have hbo := ae_restrict_of_ae (μ := μ) (s := ball p R) (G v).bounded
  filter_upwards [hre, hbo] with x hx hb
  rw [← hx]
  exact (le_abs_self _).trans hb

end RegularPointCoordinates

end

end OAI
