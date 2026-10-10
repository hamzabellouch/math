import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialEnergyMonotone

namespace OAI

/-! Zero energy on every finite radius, together with decay, forces a mode to vanish. -/

open Set Filter
open scoped ContDiff
namespace DefocusingNLS
open ProfileCertificate

theorem radialGradientEnergy_constant (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (R : ℝ) (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hE : (∫ r in (0 : ℝ)..R, radialMassDensity n z r*(deriv f r)^2)=0) :
    ∀ r ∈ Icc 0 R, f r=f R := by
  let g := fun r => f r-f R
  have hg : ContDiff ℝ 1 g := hf.sub contDiff_const
  have hd : ∀ r, deriv g r=deriv f r := by
    intro r
    exact ((hf.differentiable (by norm_num) r).hasDerivAt.sub_const (f R)).deriv
  have hEg : (∫ r in (0 : ℝ)..R, radialMassDensity n z r*(deriv g r)^2)=0 := by
    simp only [hd]
    exact hE
  intro r hr
  have h := radialGradientEnergy_zero n z hX hz R (hr.1.trans hr.2) g hg
    (by dsimp [g]; ring) hEg r hr
  dsimp [g] at h
  linarith

theorem radialScalarForm_all_zero_of_decay (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (q f : ℝ → ℝ)
    (hqn : ∀ r, 0 ≤ r → 0 ≤ q r) (hf : ContDiff ℝ 1 f)
    (hlim : Tendsto f atTop (nhds 0))
    (hE : ∀ R, 0 ≤ R → radialScalarForm n z R q f f=0) :
    ∀ r, 0 ≤ r → f r=0 := by
  have hG : ∀ R, 0 ≤ R →
      (∫ r in (0 : ℝ)..R, radialMassDensity n z r*(deriv f r)^2)=0 := by
    intro R hR
    have hGn : 0 ≤ ∫ r in (0 : ℝ)..R, radialMassDensity n z r*(deriv f r)^2 := by
      apply intervalIntegral.integral_nonneg hR
      intro r hr
      have hr0 := hr.1
      unfold radialMassDensity
      positivity
    have hPn : 0 ≤ ∫ r in (0 : ℝ)..R, radialMassDensity n z r*q r*(f r)^2 := by
      apply intervalIntegral.integral_nonneg hR
      intro r hr
      have hr0 := hr.1
      have hqr := hqn r hr0
      unfold radialMassDensity
      positivity
    have he := hE R hR
    rw [radialScalarForm_diag] at he
    linarith
  intro r hr
  have heq : ∀ᶠ R in atTop, f R=f r := by
    filter_upwards [eventually_ge_atTop r] with R hR
    exact (radialGradientEnergy_constant n z hX hz R f hf (hG R (hr.trans hR)) r
      ⟨hr,hR⟩).symm
  have hconst : Tendsto f atTop (nhds (f r)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [heq] with R hR
    exact hR.symm
  exact tendsto_nhds_unique hconst hlim

end DefocusingNLS

end OAI
