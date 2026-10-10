import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.DyadicFitCalibration
import OAI.Analysis.RieszRectifiability.Foundations.UniformDistanceTransfer

namespace OAI

/-!
# Distance transfer between adjacent dyadic plane fits

Calibrated fitting errors and lower mass bounds give distance comparisons between
successive affine planes. A uniform smallness threshold on the final dyadic error
controls every adjacent step, with constants chosen before the measure and planes.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem exists_uniform_dyadic_distance_steps (n d : ℕ)
    (C c b : ℝ) (hC : 0 ≤ C) (hc : 0 < c) (hb : 1 < b) :
    ∃ B κ : ℝ, 0 < B ∧ 0 < κ ∧
      ∀ μ : Measure (Ambient d), IsFiniteMeasureOnCompacts μ → GlobalUpperGrowth n C μ →
      ∀ N : ℕ, ∀ δ : ℝ, 0 < δ → δ * b ^ N ≤ κ →
      ∀ P : ℕ → AffineSubspace ℝ (Ambient d), (∀ i, IsAffineNPlane n (P i)) →
      (∀ i ≤ N, c * ((2 : ℝ) ^ i) ^ n ≤ μ.real (ball (0 : Ambient d) ((2 : ℝ) ^ i))) →
      (∀ i ≤ N, (∫ x in ball (0 : Ambient d) ((2 : ℝ) ^ i),
        infDist x (P i : Set (Ambient d)) ^ 2 ∂μ) ≤
          2 * (δ * b ^ i) ^ 2 * ((2 : ℝ) ^ i) ^ (n + 2)) →
      ∀ i < N, ∀ x : Ambient d,
        infDist x (P i : Set (Ambient d)) ≤ infDist x (P (i + 1) : Set (Ambient d)) +
          B * δ * (2 : ℝ) ^ i * b ^ i * (3 + ‖x‖ / (2 : ℝ) ^ i) := by
  obtain ⟨A, ε, hA, hε, _hε1, htransfer⟩ := exists_uniform_measured_distance_transfer n d C c hC hc
  obtain ⟨L, hL, hcal⟩ := exists_dyadic_fit_calibration n b c hc
  let B := A * L
  let κ := ε / L
  refine ⟨B, κ, mul_pos hA hL, div_pos hε hL, ?_⟩
  intro μ hfinite hg N δ hδ hsmall P hP hmass hfit i hi x
  let : IsFiniteMeasureOnCompacts μ := hfinite
  let η := L * δ * (2 : ℝ) ^ i * b ^ i
  have hη : 0 < η := by dsimp only [η]; positivity
  have hsmallL : L * δ * b ^ N ≤ ε := by
    have h := (le_div_iff₀ hL).mp hsmall
    nlinarith
  have hηsmall : η ≤ ε * (2 : ℝ) ^ i :=
    calibrated_dyadic_threshold_small L δ b ε hL.le hδ.le hb.le N i hi.le hsmallL
  have hjoint := calibrated_dyadic_joint_fit_error μ P hP δ b L c hcal N hfit i hi
  have hreverse : (∫ y in ball (0 : Ambient d) ((2 : ℝ) ^ i),
      jointPlaneFitError (P (i + 1)) (P i) y ∂μ) ≤ η ^ 2 * ((c / 2) * ((2 : ℝ) ^ i) ^ n) := by
    simpa only [jointPlaneFitError, add_comm] using! hjoint
  have h := htransfer μ hfinite hg ((2 : ℝ) ^ i) (by positivity) (hmass i hi.le)
    (P (i + 1)) (P i) (hP (i + 1)) (hP i) η hη hηsmall hreverse x
  convert! h using 1
  dsimp only [B, η]
  ring

end

end RieszRectifiability

end OAI
