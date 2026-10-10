import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialAngularEstimates
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialAngularScalar
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialZeroEnergyDecay

namespace OAI

/-! Coercivity and zero-energy consequences for the full angular scalar form. -/

open Set Filter
open scoped ContDiff
namespace DefocusingNLS
open ProfileCertificate

theorem radialAngularScalarForm_nonneg (n : ℕ) (z : ProfileMatchingBall) (η R : ℝ)
    (hη : 0 ≤ η) (hR : 0 ≤ R) (q f : ℝ → ℝ) (hq : ∀ r ∈ Icc 0 R, 0 ≤ q r) :
    0 ≤ radialAngularScalarForm n z η R q f f :=
  add_nonneg (radialScalarForm_nonneg n z R hR q f hq)
    (mul_nonneg hη (radialAngularForm_nonneg n z R hR f))

theorem radialAngularScalarForm_mono (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (η : ℝ) (hη : 0 ≤ η)
    (q f : ℝ → ℝ) (hq : Continuous q) (hqn : ∀ r, 0 ≤ r → 0 ≤ q r) (hf : ContDiff ℝ 1 f) :
    MonotoneOn (fun R => radialAngularScalarForm n z η R q f f) (Ici 0) := by
  intro R hR S hS hRS
  exact add_le_add (radialScalarForm_mono n z hX hz q f hq hqn hf hR hS hRS)
    (mul_le_mul_of_nonneg_left
      (radialAngularForm_mono n z hX hz f hf.continuous hR hS hRS) hη)

theorem radialAngularScalarForm_all_zero_of_decay (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (η : ℝ) (hη : 0 ≤ η) (q f : ℝ → ℝ)
    (hqn : ∀ r, 0 ≤ r → 0 ≤ q r) (hf : ContDiff ℝ 1 f)
    (hlim : Tendsto f atTop (nhds 0))
    (hE : ∀ R, 0 ≤ R → radialAngularScalarForm n z η R q f f=0) :
    ∀ r, 0 ≤ r → f r=0 := by
  apply radialScalarForm_all_zero_of_decay n z hX hz q f hqn hf hlim
  intro R hR
  have he := hE R hR
  have hA := mul_nonneg hη (radialAngularForm_nonneg n z R hR f)
  have hB := radialScalarForm_nonneg n z R hR q f (fun r hr => hqn r hr.1)
  unfold radialAngularScalarForm at he
  linarith

theorem radialAngularScalarForm_coercive_of_base (n : ℕ) (z : ProfileMatchingBall)
    (η R σ C H : ℝ) (hη : 0 ≤ η) (hR : 0 ≤ R) (hσ : 4 ≤ σ)
    (q dq f : ℝ → ℝ) (hv : ∀ r ∈ Icc 0 R, 0 ≤ radialMatchedVelocityRatio n z r)
    (hbase : (3/4 : ℝ)*radialScalarForm n z R q f f ≤
      σ*radialScalarForm n z R q f f+radialScalarVirial n z R q dq f+C*H) :
    (3/4 : ℝ)*radialAngularScalarForm n z η R q f f ≤
      σ*radialAngularScalarForm n z η R q f f+radialAngularScalarVirial n z η R q dq f+C*H := by
  have hA := mul_le_mul_of_nonneg_left (radialAngularForm_coercive n z R σ hR hσ f hv) hη
  unfold radialAngularScalarForm radialAngularScalarVirial
  nlinarith only [hbase,hA]

theorem radialAngularScalarBoundary_tendsto (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (η s t : ℝ) (q f g : ℝ → ℝ)
    (hM : radialMassDensity n z =O[atTop] (fun r : ℝ => r^(11 : ℝ)))
    (hF : radialMassFlux n z =O[atTop] (fun r : ℝ => r^(12 : ℝ)))
    (hq : q =O[atTop] (fun r : ℝ => r^(0 : ℝ)))
    (hK : radialAngularDensity n z =O[atTop] (fun r : ℝ => r^(9 : ℝ)))
    (hf : HasRadialEnergyDecay f) (hg : HasRadialEnergyDecay g) :
    Tendsto (fun R => radialAngularScalarBoundary n z η R s t q f g) atTop (nhds 0) := by
  have hB := radialSpectralBoundary_tendsto n z s t q f g hM hF hq hf hg
  have hA := radialAngularBoundary_tendsto n z hX hz f hf hK
  simpa only [radialAngularScalarBoundary,mul_zero,add_zero] using hB.add (hA.const_mul η)

end DefocusingNLS

end OAI
