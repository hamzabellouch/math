import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreeExteriorSmoothness
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPhysicalJet

namespace OAI

/-! The actual free H profile solves the stationary radial equation in physical radius. -/

open Set Filter
namespace DefocusingNLS
open ProfileCertificate

noncomputable def radialShootingFreeJet (z : ProfileMatchingBall) : ℝ → ℂ × ℂ :=
  spectralPhysicalJet (-2*radialShootingQ z) (radialFreeSlowJet (radialShootingQ z) (radialShootingM z))

theorem radialShootingFreeJet_fst (z : ProfileMatchingBall) (r : ℝ) :
    (radialShootingFreeJet z r).1=radialShootingFreeExterior z r := rfl

theorem radialShootingFreeJet_hasDerivAt (z : ProfileMatchingBall) (r : ℝ) (hr : 0 < r) :
    HasDerivAt (radialShootingFreeJet z)
      ((radialShootingFreeJet z r).2,
       -radialFreeCoefficient r*(radialShootingFreeJet z r).2-
         (radialShootingB (profileMatchingParameter z) : ℂ)*(radialShootingFreeJet z r).1) r := by
  let q := radialShootingQ z
  let J := radialFreeSlowJet q (radialShootingM z)
  have hq : -1 < q.re := by simp [q,radialShootingQ]
  have hJ : HasDerivAt J ((J (Real.log r)).2,
      -(2*(-2*q)+10)*(J (Real.log r)).2-
      ((-2*q)*((-2*q)+10)-0)*(J (Real.log r)).1-
      1*Complex.I*(Real.exp (2*Real.log r)/2 : ℝ)*(J (Real.log r)).2+0) (Real.log r) := by
    apply (radialFreeSlowJet_hasDerivAt q (radialShootingM z) hq (Real.log r)).congr_deriv
    apply Prod.ext
    · simp [J,radialExteriorErrorMatrix]
    · simp only [Prod.snd_add,radialExteriorErrorMatrix,ContinuousLinearMap.prod_apply,
        neg_apply,add_apply,smul_apply,ContinuousLinearMap.coe_fst',
        ContinuousLinearMap.coe_snd',smul_eq_mul]
      dsimp only [J]
      ring
  apply (spectralPhysicalJet_hasDerivAt 1 (-2*q) 0 J r hr 0 hJ).congr_deriv
  apply Prod.ext
  · rfl
  · dsimp only [radialFreeCoefficient,radialShootingFreeJet,J,q,radialShootingQ]
    push_cast
    ring_nf
    simp only [Complex.I_sq]
    ring

theorem radialShootingFreeExterior_hasDerivAt (z : ProfileMatchingBall) (r : ℝ) (hr : 0 < r) :
    HasDerivAt (radialShootingFreeExterior z) (radialShootingFreeJet z r).2 r :=
  (radialShootingFreeJet_hasDerivAt z r hr).fst

theorem radialShootingFreeExterior_hasDerivAt_deriv (z : ProfileMatchingBall) (r : ℝ) (hr : 0 < r) :
    HasDerivAt (deriv (radialShootingFreeExterior z))
      (-radialFreeCoefficient r*deriv (radialShootingFreeExterior z) r-
        (radialShootingB (profileMatchingParameter z) : ℂ)*radialShootingFreeExterior z r) r := by
  have he : deriv (radialShootingFreeExterior z) =ᶠ[nhds r] fun x => (radialShootingFreeJet z x).2 := by
    filter_upwards [Ioi_mem_nhds hr] with x hx
    exact (radialShootingFreeExterior_hasDerivAt z x hx).deriv
  have hd₀ : HasDerivAt (fun x => (radialShootingFreeJet z x).2)
      (-radialFreeCoefficient r*(radialShootingFreeJet z r).2-
        (radialShootingB (profileMatchingParameter z) : ℂ)*(radialShootingFreeJet z r).1) r :=
    (radialShootingFreeJet_hasDerivAt z r hr).snd
  have hd := hd₀.congr_of_eventuallyEq he
  simpa only [(radialShootingFreeExterior_hasDerivAt z r hr).deriv,radialShootingFreeJet_fst] using hd

end DefocusingNLS

end OAI
