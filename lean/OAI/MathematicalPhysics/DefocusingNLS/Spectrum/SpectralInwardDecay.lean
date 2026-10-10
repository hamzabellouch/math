import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralInwardMass
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace OAI

/-! Quantitative decay under an inward complex slope and a bounded error. -/

open Set
namespace DefocusingNLS

theorem spectralComplex_inward_decay (a b mu delta : ℝ) (hab : a ≤ b)
    (hmu : 0 < mu) (hdelta : 0 ≤ delta) (q dq alpha : ℝ → ℂ)
    (hq : ContinuousOn q (Icc a b))
    (hD : ∀ r ∈ Ioo a b, HasDerivAt q (dq r) r)
    (hslope : ∀ r ∈ Ioo a b, (alpha r).re ≤ -mu)
    (herror : ∀ r ∈ Ioo a b, ‖dq r-alpha r*q r‖ ≤ delta) :
    Complex.normSq (q b) ≤ Real.exp (-mu*(b-a))*Complex.normSq (q a)+(delta/mu)^2 := by
  let C := (delta/mu)^2
  let Z := fun r => Real.exp (mu*(r-a))*(Complex.normSq (q r)-C)
  have hC : 0 ≤ C := sq_nonneg _
  have hCe : mu*C = delta^2/mu := by
    dsimp only [C]
    field_simp
  have hZc : ContinuousOn Z (Icc a b) :=
    (Real.continuous_exp.comp_continuousOn
      ((continuousOn_id.sub continuousOn_const).const_mul mu)).mul
        ((Complex.continuous_normSq.comp_continuousOn hq).sub continuousOn_const)
  have hZD (r : ℝ) (hr : r ∈ Ioo a b) :
      HasDerivAt Z (Real.exp (mu*(r-a))*
        (mu*(Complex.normSq (q r)-C)+2*(star (q r)*dq r).re)) r := by
    have h := ((((hasDerivAt_id r).sub_const a).const_mul mu).exp).mul
      ((spectralComplex_normSq_hasDerivAt q (dq r) r (hD r hr)).sub_const C)
    apply h.congr_deriv
    dsimp only [id_eq]
    ring
  have hanti : AntitoneOn Z (Icc a b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a b) hZc
    · intro r hr
      have hr' : r ∈ Ioo a b := by simpa only [interior_Icc] using hr
      exact (hZD r hr').differentiableAt.differentiableWithinAt
    · intro r hr
      have hr' : r ∈ Ioo a b := by simpa only [interior_Icc] using hr
      rw [(hZD r hr').deriv]
      apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
      have hm := spectralComplex_inward_mass (q r) (dq r) (alpha r) mu delta hmu hdelta
        (hslope r hr') (herror r hr')
      nlinarith only [hm,hCe]
  have hz := hanti ⟨le_rfl,hab⟩ ⟨hab,le_rfl⟩ hab
  change Real.exp (mu*(b-a))*(Complex.normSq (q b)-C) ≤
    Real.exp (mu*(a-a))*(Complex.normSq (q a)-C) at hz
  simp only [sub_self,mul_zero,Real.exp_zero,one_mul] at hz
  have hh := mul_le_mul_of_nonneg_left hz (Real.exp_pos (-mu*(b-a))).le
  have hex : Real.exp (-mu*(b-a))*Real.exp (mu*(b-a)) = 1 := by
    rw [← Real.exp_add]
    rw [show -mu*(b-a)+mu*(b-a) = 0 by ring,Real.exp_zero]
  rw [← mul_assoc,hex,one_mul] at hh
  change Complex.normSq (q b) ≤ Real.exp (-mu*(b-a))*Complex.normSq (q a)+C
  nlinarith only [hh,mul_nonneg (Real.exp_pos (-mu*(b-a))).le hC]

end DefocusingNLS

end OAI
