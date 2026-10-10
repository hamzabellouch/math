import OAI.Geometry.RCD.Metric.ScaledMassBackground
import OAI.Geometry.RCD.Sobolev.ResidualBochnerMass
import OAI.Geometry.RCD.Heat.HeatRegimeBridges

namespace OAI

/-! # The actual local Bochner mass has a uniform scaled bound -/

open Set Metric MeasureTheory
open scoped NNReal InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (hQ : QuadraticCheegerEnergy μ)

/-- A larger good cutoff bounds only the local full measure needed by
coarse dyadic balls; its exterior extension plays no role. -/
theorem harmonic_scaled_local_mass_bound {n : ℕ} {p : X} {R κ C B V : ℝ}
    (hR : 0 < R) (hκ : 0 ≤ κ) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hcurv : κ * R ^ 2 ≤ 1)
    (U : Euclidean n →L[ℝ] SobolevSpace μ hQ) (M : PositiveBilinearMeasure X (Euclidean n)) (L : ℝ≥0)
    (G : ∀ v, LocalHarmonicEnergy μ hQ U M κ p (4 * R) L v)
    (χ : GoodLaplacianCutoff μ hQ p (2 * R) C)
    (hL : (L : ℝ) ^ 2 ≤ B)
    (hvolume : μ.real (closedBall p (4 * R)) ≤ V * (5 * R) ^ n) (v : Euclidean n) :
    ⟪v, M.massOperator (ball p (2 * R)) v⟫_ℝ ≤
      ((C / 8 + 1) * B * V * 5 ^ n) * (R ^ n / R ^ 2) * ‖v‖ ^ 2 := by
  have hg : ∀ᵐ x ∂μ.restrict (closedBall p (4 * R)),
      localGamma μ hQ (U v) (U v) x ≤ (L : ℝ) ^ 2 * ‖v‖ ^ 2 := by
    have hb := LocalHarmonicEnergy.gamma_bound_on_smaller_ball μ hQ G
      (show 8 * R ≤ 2 * (4 * R) by linarith) v
    exact ae_restrict_of_ae_restrict_of_subset
      (closedBall_subset_ball (show 4 * R < 8 * R by linarith)) hb
  have hm := χ.mass_le_of_gradient μ hQ (show 0 < 2 * R by positivity)
    (show 2 * R < 4 * R by linarith) hC hκ (G v)
    (by simpa only [show 2 * (2 * R) = 4 * R by ring] using hg)
  have hm' := mul_le_mul_of_nonneg_left hm (sq_nonneg R)
  have heq : R ^ 2 * (((C / (2 * R) ^ 2) / 2 + κ) *
      ((L : ℝ) ^ 2 * ‖v‖ ^ 2) * μ.real (closedBall p (2 * (2 * R)))) =
      (C / 8 + κ * R ^ 2) * (L : ℝ) ^ 2 * ‖v‖ ^ 2 * μ.real (closedBall p (4 * R)) := by
    rw [show 2 * (2 * R) = 4 * R by ring]
    field_simp [hR.ne']
    ring
  rw [heq] at hm'
  have hcurv' : C / 8 + κ * R ^ 2 ≤ C / 8 + 1 := by linarith
  have hcL : (C / 8 + κ * R ^ 2) * (L : ℝ) ^ 2 ≤ (C / 8 + 1) * B :=
    mul_le_mul hcurv' hL (sq_nonneg _) (by positivity)
  have hb := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcL (sq_nonneg ‖v‖)) (show 0 ≤ μ.real (closedBall p (4 * R)) by positivity)
  have hv := mul_le_mul_of_nonneg_left hvolume
    (show 0 ≤ (C / 8 + 1) * B * ‖v‖ ^ 2 by positivity)
  have hs : R ^ 2 * ⟪v, M.massOperator (ball p (2 * R)) v⟫_ℝ ≤
      ((C / 8 + 1) * B * V * 5 ^ n) * R ^ n * ‖v‖ ^ 2 := by
    have hh := hm'.trans (hb.trans hv)
    simpa only [mul_pow, mul_assoc, mul_comm, mul_left_comm] using hh
  have hs' : ⟪v, M.massOperator (ball p (2 * R)) v⟫_ℝ ≤
      (((C / 8 + 1) * B * V * 5 ^ n) * R ^ n * ‖v‖ ^ 2) / R ^ 2 :=
    (le_div_iff₀ (sq_pos_of_pos hR)).mpr (by simpa only [mul_comm] using hs)
  convert hs' using 1; ring

end RegularPointCoordinates

end

end OAI
