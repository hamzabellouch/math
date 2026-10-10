import OAI.MeasureTheory.Falconer.Radial.GnomonicAffinePlate
import OAI.MeasureTheory.Falconer.Radial.RadialDyadicBracket

namespace OAI

/-! # Finite-scale ball and plate bounds for the original chart law -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal

theorem dyadic_ball_all_radius {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (μ : Measure X) (N : ℕ) {L q : ℝ} (hL : 1 ≤ L) (hq : 0 ≤ q) (hμ : μ univ ≤ 1)
    (hball : ∀ x : X, ∀ j : ℕ, j ≤ N → μ (ball x (1/(2:ℝ)^j)) ≤
      ENNReal.ofReal (L*(1/(2:ℝ)^j)^q))
    (x : X) {r : ℝ} (hr : 1/(2:ℝ)^N ≤ r) :
    μ (ball x r) ≤ ENNReal.ofReal (L*(2*r)^q) := by
  have hr0 : 0 < r := (by positivity : 0 < 1/(2:ℝ)^N).trans_le hr
  by_cases hr1 : r ≤ 1
  · obtain ⟨j,hj,hrj,hjr⟩ := Regularization.dyadic_radius_bracket hr hr1
    apply ((measure_mono (ball_subset_ball hrj)).trans (hball x j hj)).trans
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) hjr hq) (by linarith))
  · have hp : 1 ≤ (2*r)^q := Real.one_le_rpow (by linarith) hq
    apply ((measure_mono (subset_univ _)).trans hμ).trans
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by nlinarith)

theorem gnomonic_dyadic_ball_bound {n : ℕ}
    (ν : Measure (Sphere (n+1))) (N : ℕ) {L q : ℝ} (hL : 1 ≤ L) (hq : 0 ≤ q)
    (hν : ν univ ≤ 1) (hνpos : ∀ᵐ (w : Sphere (n+1)) ∂ν, 0 < (w:Space (n+1)) 0)
    (hball : ∀ x : Sphere (n+1), ∀ j : ℕ, j ≤ N → ν (ball x (1/(2:ℝ)^j)) ≤
      ENNReal.ofReal (L*(1/(2:ℝ)^j)^q))
    (p : Space n) {r : ℝ} (hr : 1/(2:ℝ)^N ≤ r) :
    (Measure.map gnomonicCoordinates ν) (ball p r) ≤ ENNReal.ofReal ((L*4^q)*r^q) := by
  have hr0 : 0 < r := (by positivity : 0 < 1/(2:ℝ)^N).trans_le hr
  have hh := (gnomonicCoordinates_map_ball ν hνpos p r).trans
    (dyadic_ball_all_radius ν N hL hq hν hball (gnomonicChart p) (hr.trans (by linarith)))
  apply hh.trans_eq
  congr 1
  rw [show 2*(2*r) = 4*r by ring,Real.mul_rpow (by norm_num) hr0.le]
  ring

end Falconer

end OAI
