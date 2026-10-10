import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialSpectralCoercivity
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace OAI

/-! Vanishing weighted energy forces a radial function with zero boundary trace to vanish. -/

open Set
open scoped ContDiff
namespace DefocusingNLS
open ProfileCertificate

theorem radialGradientEnergy_zero (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (R : ℝ) (_hR : 0 ≤ R)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (hfR : f R=0)
    (hE : (∫ r in (0 : ℝ)..R, radialMassDensity n z r*(deriv f r)^2)=0) :
    ∀ r ∈ Icc 0 R, f r=0 := by
  let G := fun r => radialMassDensity n z r*(deriv f r)^2
  have hGc : Continuous G := (radialMassDensity_continuous n z hX hz).mul
    (hf.continuous_deriv_one.pow 2)
  have hGn : ∀ r ∈ Icc 0 R, 0 ≤ G r := by
    intro r hr
    have hr0 := hr.1
    dsimp [G,radialMassDensity]
    positivity
  have hdf : ∀ r ∈ Ioo 0 R, deriv f r=0 := by
    intro r hr
    by_contra hn
    have hGp : 0 < G r := by
      have hq : 0 < ‖radialMatchedProfile n z r‖ :=
        norm_pos_iff.mpr (radialMatchedProfile_ne_zero n z hX r hr.1.le)
      dsimp [G,radialMassDensity]
      exact mul_pos (mul_pos (pow_pos hr.1 11) (sq_pos_of_pos hq)) (sq_pos_of_ne_zero hn)
    have hi := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      (lt_trans hr.1 hr.2) (show ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Icc 0 R) from continuousOn_const)
      hGc.continuousOn (fun x hx => hGn x ⟨hx.1.le,hx.2⟩) ⟨r,⟨hr.1.le,hr.2.le⟩,hGp⟩
    simp only [intervalIntegral.integral_zero] at hi
    change 0 < ∫ r in (0 : ℝ)..R, G r at hi
    exact (ne_of_gt hi) hE
  intro r hr
  rcases hr.2.eq_or_lt with he | hlt
  · simpa only [he] using hfR
  · obtain ⟨c,hc,he⟩ := exists_deriv_eq_slope f hlt hf.continuous.continuousOn
      (hf.differentiable (by norm_num)).differentiableOn
    have hc0 : 0 < c := lt_of_le_of_lt hr.1 hc.1
    rw [hdf c ⟨hc0,hc.2⟩,hfR] at he
    have hn : R-r≠0 := (sub_pos.mpr hlt).ne'
    have hz' := (div_eq_zero_iff).mp he.symm
    rcases hz' with hz' | hz'
    · linarith
    · exact (hn hz').elim

theorem radialScalarForm_zero (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (R : ℝ) (hR : 0 ≤ R)
    (q f : ℝ → ℝ) (hq : ∀ r ∈ Icc 0 R, 0 ≤ q r)
    (hf : ContDiff ℝ 1 f) (hfR : f R=0)
    (hE : radialScalarForm n z R q f f=0) :
    ∀ r ∈ Icc 0 R, f r=0 := by
  have hG : 0 ≤ ∫ r in (0 : ℝ)..R, radialMassDensity n z r*(deriv f r)^2 := by
    apply intervalIntegral.integral_nonneg hR
    intro r hr
    have hr0 := hr.1
    unfold radialMassDensity
    positivity
  have hP : 0 ≤ ∫ r in (0 : ℝ)..R, radialMassDensity n z r*q r*(f r)^2 := by
    apply intervalIntegral.integral_nonneg hR
    intro r hr
    have hr0 := hr.1
    have hqr := hq r hr
    unfold radialMassDensity
    positivity
  rw [radialScalarForm_diag] at hE
  apply radialGradientEnergy_zero n z hX hz R hR f hf hfR
  linarith

end DefocusingNLS

end OAI
