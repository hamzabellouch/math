import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralInwardMass
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace OAI

/-! Integrate the scalar mass inequality needed for the coupled shell. -/

open Set
namespace DefocusingNLS

theorem spectralComplex_mass_decay (a b mu C : ℝ) (hab : a ≤ b)
    (_hmu : 0 < mu) (hC : 0 ≤ C) (q dq : ℝ → ℂ)
    (hq : ContinuousOn q (Icc a b))
    (hD : ∀ r ∈ Ioo a b, HasDerivAt q (dq r) r)
    (herror : ∀ r ∈ Ioo a b, 2*(star (q r)*dq r).re ≤ -mu*Complex.normSq (q r)+mu*C) :
    Complex.normSq (q b) ≤ Real.exp (-mu*(b-a))*Complex.normSq (q a)+C := by
  let Z := fun r => Real.exp (mu*(r-a))*(Complex.normSq (q r)-C)
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
      nlinarith only [herror r hr']
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
