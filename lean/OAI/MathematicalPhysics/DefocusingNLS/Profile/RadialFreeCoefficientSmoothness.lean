import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreeGaugeCoefficient
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedTransportSmoothness

namespace OAI

/-! Smoothness of the matched limiting coefficients on the whole open exterior. -/

open Set
open scoped ContDiff
namespace DefocusingNLS
open ProfileCertificate

theorem radialMatchedFreeMass_contDiffOn_matched (z : ProfileMatchingBall)
    (hz₁ : z.val.1=0) (hz : diskProfile (profileMatchingParameter z)=0) :
    ContDiffOn ℝ ∞ (radialMatchedFreeMassFunction z)
      (Ioi (radialShootingR (profileMatchingParameter z))) := by
  have hL : 0 < radialShootingR (profileMatchingParameter z) :=
    lt_of_lt_of_le (by norm_num) (radialShooting_geometry (profileMatchingParameter z)).2.1
  have hQ := (radialShootingFreeExterior_contDiffOn z).mono
    (fun _ hx => hL.trans hx)
  apply (hQ.norm_sq ℂ).congr
  intro r hr
  exact congrArg (fun q : ℂ => ‖q‖^2) (radialMatchedFreeProfile_eq_physical z hz₁ hz r (le_of_lt hr))

theorem radialMatchedFreeTransport_contDiffOn_matched (z : ProfileMatchingBall)
    (hz₁ : z.val.1=0) (hz : diskProfile (profileMatchingParameter z)=0)
    (hc : Continuous (radialMatchedFreeMassFunction z)) (α β : ℝ)
    (hα : radialShootingR (profileMatchingParameter z) < α) :
    ContDiffOn ℝ ∞ (radialMatchedFreeTransportFunction z) (Icc α β) := by
  let μ := radialMatchedFreeMassFunction z
  have hα0 : 0 < α := lt_trans
    (by linarith [(radialShooting_geometry (profileMatchingParameter z)).2.1]) hα
  have hμ : ContDiffOn ℝ ∞ μ (Icc α β) :=
    (radialMatchedFreeMass_contDiffOn_matched z hz₁ hz).mono
      (fun _ hr => hα.trans_le hr.1)
  have hμt : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => μ p.1) ((Icc α β) ×ˢ univ) :=
    hμ.comp contDiff_fst.contDiffOn (fun _ hp => hp.1)
  have ht : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => p.1) ((Icc α β) ×ˢ univ) := by fun_prop
  have hy : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => p.2) ((Icc α β) ×ˢ univ) := by fun_prop
  have hn (p : ℝ × ℝ) (hp : p ∈ (Icc α β) ×ˢ univ) : p.1 ≠ 0 :=
    (hα0.trans_le hp.1.1).ne'
  have hF : ContDiffOn ℝ ∞
      (fun p : ℝ × ℝ => μ p.1/p.1-12*p.2/p.1) ((Icc α β) ×ˢ univ) :=
    (hμt.div ht hn).sub ((contDiffOn_const.mul hy).div ht hn)
  have hS : ContDiffOn ℝ ∞ (radialAverage μ) (Icc α β) := by
    apply ODE.contDiffOn_enat_Icc_of_hasDerivWithinAt
      (f := fun t y => μ t/t-12*y/t) (u := (univ : Set ℝ)) hF
    · intro x hx
      exact (hasDerivAt_radialAverage μ hc x (hα0.trans_le hx.1).ne').hasDerivWithinAt
    · exact fun _ _ => mem_univ _
  exact contDiffOn_const.mul (contDiffOn_id.mul hS)

end DefocusingNLS

end OAI
