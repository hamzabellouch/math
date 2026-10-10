import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralODESmoothness
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedMultiplierLimit
import Mathlib.Analysis.InnerProductSpace.Calculus

namespace OAI

/-! The explicit free exterior and its mass are smooth away from zero. -/

open Set
open scoped ContDiff
namespace DefocusingNLS
open ProfileCertificate

theorem radialFreeSlowJet_contDiff (q m : ℂ) (hq : -1 < q.re) :
    ContDiff ℝ ∞ (radialFreeSlowJet q m) := by
  apply spectralODE_contDiff
    (fun t V => (0,-Complex.I*(Real.exp (2*t)/2 : ℝ)*V.2)+radialExteriorErrorMatrix (-2*q) V)
    (radialFreeSlowJet q m) _ (radialFreeSlowJet_hasDerivAt q m hq)
  have hM : ContDiff ℝ ∞ (fun p : ℝ × (ℂ × ℂ) => radialExteriorErrorMatrix (-2*q) p.2) :=
    (radialExteriorErrorMatrix (-2*q)).contDiff.comp contDiff_snd
  have hE : ContDiff ℝ ∞ (fun p : ℝ × (ℂ × ℂ) =>
      ((0 : ℂ),-Complex.I*(Real.exp (2*p.1)/2 : ℝ)*p.2.2)) := by
    have hr : ContDiff ℝ ∞ (fun p : ℝ × (ℂ × ℂ) => Real.exp (2*p.1)/2) := by fun_prop
    have hc := Complex.ofRealCLM.contDiff.comp hr
    exact contDiff_const.prodMk ((contDiff_const.mul hc).mul contDiff_snd.snd)
  exact hE.add hM

theorem radialShootingFreeExterior_contDiffOn (z : ProfileMatchingBall) :
    ContDiffOn ℝ ∞ (radialShootingFreeExterior z) (Ioi 0) := by
  have hq : -1 < (radialShootingQ z).re := by simp [radialShootingQ]
  have hlog : ContDiffOn ℝ ∞ Real.log (Ioi (0 : ℝ)) :=
    Real.contDiffOn_log.mono (fun x hx => hx.ne')
  have hExp : ContDiffOn ℝ ∞
      (fun r : ℝ => Complex.exp ((-2*radialShootingQ z)*(Real.log r : ℂ))) (Ioi 0) :=
    Complex.contDiff_exp.comp_contDiffOn
      (contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn hlog))
  exact hExp.mul ((radialFreeSlowJet_contDiff _ _ hq).fst.comp_contDiffOn hlog)

theorem radialMatchedFreeMass_contDiffOn_exterior (z : ProfileMatchingBall) :
    ContDiffOn ℝ ∞ (radialMatchedFreeMassFunction z) (Ioi innerBoundaryRadius) := by
  have hR : 0 < innerBoundaryRadius := by linarith [innerBoundaryRadius_bounds.1]
  have hf := (radialShootingFreeExterior_contDiffOn z).mono
    (fun _ hx => hR.trans hx)
  apply (hf.norm_sq ℂ).congr
  intro x hx
  change innerBoundaryRadius < x at hx
  simp only [radialMatchedFreeMassFunction,radialMatchedFreeProfile,ite_eq_right (not_le.mpr hx)]

end DefocusingNLS

end OAI
