import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPhase
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialGreenOperator
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPotentialDifference

namespace OAI

/-! A continuous positive extension defines the phase without altering the inner velocity. -/

open Set Filter Topology
namespace DefocusingNLS

noncomputable def radialClampedAmplitude (R : ℝ) (A : ℝ → ℝ) (r : ℝ) : ℝ :=
  A (radialClamp R r)

theorem radialClampedAmplitude_continuous (R : ℝ) (A : ℝ → ℝ) (hA : Continuous A) :
    Continuous (radialClampedAmplitude R A) := hA.comp (continuous_radialClamp R)

theorem radialClampedAmplitude_eq (R : ℝ) (A : ℝ → ℝ) (r : ℝ) (hr : r ∈ Icc 0 R) :
    radialClampedAmplitude R A r=A r := by
  unfold radialClampedAmplitude
  rw [radialClamp_eq R r hr]

theorem radialClampedAmplitude_hasDerivAt (R : ℝ) (A : ℝ → ℝ) (hA : Differentiable ℝ A)
    (r : ℝ) (hr : r ∈ Ioo 0 R) : HasDerivAt (radialClampedAmplitude R A) (deriv A r) r := by
  apply (hA r).hasDerivAt.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hr] with t ht
  exact radialClampedAmplitude_eq R A t ⟨ht.1.le,ht.2.le⟩

theorem radialVelocityRatio_clamped_eq (c R : ℝ) (A : ℝ → ℝ) (r : ℝ) (hr : r ∈ Icc 0 R) :
    radialVelocityRatio c (radialClampedAmplitude R A) r=radialVelocityRatio c A r := by
  have hav := radialAverage_congr (fun t => (radialClampedAmplitude R A t)^2)
    (fun t => (A t)^2) r hr.1 (by
      intro t ht
      change (radialClampedAmplitude R A t)^2=(A t)^2
      rw [radialClampedAmplitude_eq R A t ⟨ht.1,ht.2.trans hr.2⟩])
  simp only [radialVelocityRatio,hav,radialClampedAmplitude_eq R A r hr]

theorem radialVelocity_clamped_eq (c R : ℝ) (A : ℝ → ℝ) (r : ℝ) (hr : r ∈ Icc 0 R) :
    radialVelocity c (radialClampedAmplitude R A) r=radialVelocity c A r := by
  simp only [radialVelocity,radialVelocityRatio_clamped_eq c R A r hr]

end DefocusingNLS

end OAI
