import OAI.Geometry.RCD.Sobolev.NestedBallCutoff
import OAI.Geometry.RCD.Harmonic.HarmonicRecoveryStrong

namespace OAI

/-! # Strong weighted recovery controls the entire fixed core ball -/

open Set Metric Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem cutoff_energy_core_convergence (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
    {a b R : ℝ} (hab : a<b) (hbR : b<R)
    (p : ℕ → X) (r c : ℕ → ℝ) (hr : ∀ k, 0<r k) (hc : ∀ k, 0≤c k)
    (u : ℕ → SobolevSpace μ hQ)
    (hlim : Tendsto (fun k => c k*∫ x in ball (p k) (R*r k),
      (nestedBallCutoff (p k) (a*r k) (b*r k) x)^2*localGamma μ hQ (u k) (u k) x ∂μ)
      atTop (𝓝 0)) :
    Tendsto (fun k => c k*∫ x in ball (p k) (a*r k), localGamma μ hQ (u k) (u k) x ∂μ)
      atTop (𝓝 0) := by
  have hnonneg (k : ℕ) : ∀ᵐ x ∂μ, 0≤localGamma μ hQ (u k) (u k) x := by
    filter_upwards [localGamma_self μ hQ (u k)] with x hx
    rw [hx]
    positivity
  apply squeeze_zero (fun k => mul_nonneg (hc k) (integral_nonneg_of_ae (ae_restrict_of_ae (hnonneg k))))
    (fun k => ?_) hlim
  let χ := nestedBallCutoff (p k) (a*r k) (b*r k)
  have hi : Integrable (fun x => (χ x)^2*localGamma μ hQ (u k) (u k) x) μ := by
    apply (localGamma_memL1 μ hQ (u k) (u k)).bdd_mul
      ((nestedBallCutoff_lipschitz (p k) (mul_lt_mul_of_pos_right hab (hr k))).continuous.aestronglyMeasurable.pow 2)
    exact Eventually.of_forall fun x => by
      have hh := nestedBallCutoff_bounds (p k) (a*r k) (b*r k) x
      change ‖(χ x)^2‖≤(1:ℝ)
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      dsimp only [χ]
      nlinarith
  have he : (∫ x in ball (p k) (a*r k), localGamma μ hQ (u k) (u k) x ∂μ)=
      ∫ x in ball (p k) (a*r k), (χ x)^2*localGamma μ hQ (u k) (u k) x ∂μ := by
    apply setIntegral_congr_fun measurableSet_ball
    intro x hx
    change localGamma μ hQ (u k) (u k) x=(χ x)^2*localGamma μ hQ (u k) (u k) x
    rw [show χ x=1 from nestedBallCutoff_eq_one (p k) (mul_lt_mul_of_pos_right hab (hr k))
      (by simpa only [dist_comm] using hx.le)]
    ring
  apply mul_le_mul_of_nonneg_left _ (hc k)
  rw [he]
  apply setIntegral_mono_set hi.restrict
  · exact (ae_restrict_of_ae (hnonneg k)).mono fun x hx => mul_nonneg (sq_nonneg _) hx
  · exact Eventually.of_forall (ball_subset_ball (mul_le_mul_of_nonneg_right (hab.trans hbR).le (hr k).le))

end RegularPointCoordinates

end

end OAI
