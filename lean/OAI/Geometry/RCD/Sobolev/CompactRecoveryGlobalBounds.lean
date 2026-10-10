import OAI.Geometry.RCD.Sobolev.SupportedGammaIntegral
import OAI.Geometry.RCD.Metric.ContainingMassUniformL2
import OAI.Geometry.RCD.Sobolev.DirichletPoincare

namespace OAI

/-! # Global normalized L2 and energy bounds for the compact recoveries -/

open Set Metric Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem compact_recovery_global_bounds (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
    {S c B Q : ℝ} (hcS : c≤S)
    (p : ℕ → X) (r : ℕ → ℝ) (hr : ∀ k, 0≤r k)
    [∀ k, IsFiniteMeasure (μ.restrict (ball (p k) (S*r k)))]
    (u : ℕ → SobolevSpace μ hQ) (v : ℕ → X → ℝ)
    (hv : ∀ k x, |v k x|≤B)
    (hconv : ∀ᶠ k in atTop, ∀ᵐ x ∂μ.restrict (ball (p k) (S*r k)),
      |SobolevSpace.toLp μ hQ (u k) x-v k x|≤1)
    (hz : ∀ k, ∀ᵐ x ∂μ, x∉ball (p k) (c*r k) → SobolevSpace.toLp μ hQ (u k) x=0)
    (hg : ∀ᶠ k in atTop, ∀ᵐ x ∂μ, r k^2*localGamma μ hQ (u k) (u k) x≤Q^2) :
    ∀ᶠ k in atTop,
      ‖SobolevSpace.toLp μ hQ (u k)‖^2≤(B+1)^2*μ.real (ball (p k) (S*r k)) ∧
      r k^2*energyForm μ hQ (u k) (u k)≤Q^2*μ.real (ball (p k) (S*r k)) := by
  filter_upwards [hconv,hg] with k hk hkg
  let U := ball (p k) (S*r k)
  have hzU : ∀ᵐ x ∂μ, x∉U → SobolevSpace.toLp μ hQ (u k) x=0 :=
    (hz k).mono fun x hx hn => hx (fun hh => hn ((ball_subset_ball (mul_le_mul_of_nonneg_right hcS (hr k))) hh))
  have hLp : (∫ x in U, (SobolevSpace.toLp μ hQ (u k) x)^2 ∂μ)=‖SobolevSpace.toLp μ hQ (u k)‖^2 := by
    rw [setIntegral_eq_integral_of_ae_compl_eq_zero (hzU.mono fun x hx hn => by rw [hx hn]; norm_num),
      lp_integral_square_eq_norm_square]
  constructor
  · rw [← hLp]
    have hbnd : ∀ᵐ x ∂μ.restrict U, (SobolevSpace.toLp μ hQ (u k) x)^2≤(B+1)^2 := by
      filter_upwards [hk] with x hx
      have hnorm : |SobolevSpace.toLp μ hQ (u k) x|≤B+1 := by
        calc _ = |(SobolevSpace.toLp μ hQ (u k) x-v k x)+v k x| := by congr 1; ring
             _ ≤ |SobolevSpace.toLp μ hQ (u k) x-v k x|+|v k x| := abs_add_le _ _
             _ ≤ B+1 := by linarith [hv k x]
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hnorm 2
    have hi := integral_mono_ae (((Lp.memLp (SobolevSpace.toLp μ hQ (u k))).restrict U).integrable_sq)
      (integrable_const ((B+1)^2)) hbnd
    simpa only [integral_const,Measure.real,Measure.restrict_apply_univ,smul_eq_mul,mul_comm] using hi
  · have hint : (∫ x in U, localGamma μ hQ (u k) (u k) x ∂μ)=energyForm μ hQ (u k) (u k) := by
      rw [supported_gamma_integral μ hQ (u k) (u k) U hzU,integral_localGamma_eq_energyForm]
    have hi := integral_mono_ae (((localGamma_memL1 μ hQ (u k) (u k)).restrict (s := U)).const_mul (r k^2))
      (integrable_const (Q^2)) (ae_restrict_of_ae hkg)
    rw [integral_const_mul,hint] at hi
    simpa only [integral_const,Measure.real,Measure.restrict_apply_univ,smul_eq_mul,mul_comm] using hi

end RegularPointCoordinates

end

end OAI
