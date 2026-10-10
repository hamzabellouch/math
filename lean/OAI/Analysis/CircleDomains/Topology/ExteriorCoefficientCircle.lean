import OAI.Analysis.CircleDomains.Uniformization.PrincipalTaylorCoefficients
import OAI.Analysis.CircleDomains.Reflection.HolomorphicCircleBessel

namespace OAI

/-! The full finite coefficient lower bound on each exterior circle,
retaining the actual Laurent coefficients and the derivative energy. -/
open Set Filter Function Metric Real MeasureTheory Asymptotics Bornology
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

def principalLaurentCoefficient (F : ℂ → ℂ) (n : ℕ) : ℂ :=
  diskTaylorCoefficient (invertedPrincipalRemainder F) (n+1)

lemma invertedPrincipalDerivative_analyticOnNhd {F : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (hF : DifferentiableOn ℂ F {z | R < ‖z‖})
    (ht : Tendsto (fun z => F z-z) (cobounded ℂ) (𝓝 0)) :
    AnalyticOnNhd ℂ (invertedPrincipalDerivative F) (ball 0 R⁻¹) := by
  have hu := invertedPrincipalRemainder_analyticOnNhd hR hF ht
  intro w hw
  exact analyticAt_const.sub ((analyticAt_id.pow 2).mul (hu w hw).deriv)

lemma exterior_derivative_inverse_circle_average {F : ℂ → ℂ} {R r : ℝ}
    (hR : 0 < R) (hF : DifferentiableOn ℂ F {z | R < ‖z‖}) (hr : R < r) :
    circleAverage (fun z => ‖deriv F z‖^2) 0 r =
      circleAverage (fun w => ‖invertedPrincipalDerivative F w‖^2) 0 r⁻¹ := by
  rw [← circleAverage_comp_inv]
  apply circleAverage_congr_sphere
  intro z hz
  have hzn : ‖z‖ = r := by
    simpa only [mem_sphere, dist_zero_right, abs_of_pos (hR.trans hr)] using hz
  have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (by rw [hzn]; exact (hR.trans hr).ne')
  have hdz : DifferentiableAt ℂ F z⁻¹⁻¹ := by
    simpa only [inv_inv] using (hF z (by simpa only [mem_ofPred_eq, hzn] using hr)).differentiableAt
      ((isOpen_lt continuous_const continuous_norm).mem_nhds (by simpa only [mem_ofPred_eq, hzn] using hr))
  dsimp only
  rw [invertedPrincipalDerivative_eq (inv_ne_zero hz0) hdz, inv_inv]

lemma exterior_derivative_finite_coefficients {F : ℂ → ℂ} {R r : ℝ}
    (hR : 0 < R) (hF : DifferentiableOn ℂ F {z | R < ‖z‖})
    (ht : Tendsto (fun z => F z-z) (cobounded ℂ) (𝓝 0)) (hr : R < r) (N : ℕ) :
    1 + ∑ n ∈ Finset.range N, ((n : ℝ)+1)^2 * ‖principalLaurentCoefficient F n‖^2 *
      (r⁻¹)^(2*(n+2)) ≤ circleAverage (fun z => ‖deriv F z‖^2) 0 r := by
  have hrp : 0 < r := hR.trans hr
  have hu := invertedPrincipalRemainder_analyticOnNhd hR hF ht
  have hg := invertedPrincipalDerivative_analyticOnNhd hR hF ht
  have hsub : closedBall (0 : ℂ) r⁻¹ ⊆ ball 0 R⁻¹ := by
    apply closedBall_subset_ball
    exact (inv_lt_inv₀ hrp hR).mpr hr
  have hb := holomorphic_circle_bessel (inv_pos.mpr hrp) (hg.differentiableOn.mono hsub)
    (insert 0 ((Finset.range N).image (fun n => n+2)))
  rw [exterior_derivative_inverse_circle_average hR hF hr]
  have hz : 0 ∉ (Finset.range N).image (fun n => n+2) := by simp
  rw [Finset.sum_insert hz, Finset.sum_image (by intro a _ b _ hab; change a+2 = b+2 at hab; omega)] at hb
  have hc0 : diskTaylorCoefficient (invertedPrincipalDerivative F) 0 = 1 := by
    simp [diskTaylorCoefficient, invertedPrincipalDerivative]
  simp only [hc0, norm_one, one_pow, mul_one, Nat.mul_zero, pow_zero] at hb
  convert hb using 1
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  rw [invertedPrincipalDerivative_coefficient (hu 0 (by simpa using inv_pos.mpr hR)),
    norm_mul, norm_neg]
  have hn : ‖(n+1 : ℂ)‖ = (n : ℝ)+1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using Complex.norm_natCast (n+1)
  rw [hn]
  dsimp only [principalLaurentCoefficient]
  ring

end CircleDomainRigidity

end

end OAI
