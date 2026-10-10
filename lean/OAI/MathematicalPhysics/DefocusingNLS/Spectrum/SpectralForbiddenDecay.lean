import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralScalarModulus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace OAI

/-! Terminal inward data force exponential mass decay across an entire
forbidden interval. No division by the solution is used. -/

open Set
namespace DefocusingNLS

theorem spectralForbidden_mass_decay (a b mu : ℝ) (hab : a ≤ b) (_hmu : 0 < mu)
    (q : ℝ → ℂ × ℂ) (V : ℝ → ℂ) (hq : ContinuousOn q (Icc a b))
    (hD : ∀ r ∈ Ioo a b, HasDerivAt q (spectralScalarField (V r) (q r)) r)
    (hV : ∀ r ∈ Ioo a b, (V r).re ≤ -mu^2/2)
    (hterminal : 2*spectralScalarMomentum (q b)+mu*spectralScalarMass (q b) ≤ 0) :
    spectralScalarMass (q b) ≤ Real.exp (-mu*(b-a))*spectralScalarMass (q a) := by
  let M := fun r => spectralScalarMass (q r)
  let P := fun r => spectralScalarMomentum (q r)
  let G := fun r => 2*P r+mu*M r
  have hMc : ContinuousOn M (Icc a b) := Complex.continuous_normSq.comp_continuousOn hq.fst
  have hPc : ContinuousOn P (Icc a b) := Complex.continuous_re.comp_continuousOn (hq.fst.star.mul hq.snd)
  have hMD (r : ℝ) (hr : r ∈ Ioo a b) : HasDerivAt M (2*P r) r :=
    spectralScalarMass_hasDerivAt q (V r) r (hD r hr)
  have hPD (r : ℝ) (hr : r ∈ Ioo a b) :
      HasDerivAt P (Complex.normSq (q r).2-(V r).re*M r) r :=
    spectralScalarMomentum_hasDerivAt q (V r) r (hD r hr)
  let Y := fun r => Real.exp (-mu*(r-a))*G r
  have hYc : ContinuousOn Y (Icc a b) :=
    (Real.continuous_exp.comp_continuousOn
      ((continuousOn_id.sub continuousOn_const).const_mul (-mu))).mul
        ((hPc.const_mul 2).add (hMc.const_mul mu))
  have hYD (r : ℝ) (hr : r ∈ Ioo a b) :
      HasDerivAt Y (Real.exp (-mu*(r-a))*(2*Complex.normSq (q r).2+
        (-2*(V r).re-mu^2)*M r)) r := by
    have h := ((((hasDerivAt_id r).sub_const a).const_mul (-mu)).exp).mul
      (((hPD r hr).const_mul 2).add ((hMD r hr).const_mul mu))
    apply h.congr_deriv
    dsimp only [G,id_eq,Pi.add_apply]
    ring
  have hmono : MonotoneOn Y (Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b) hYc
    · intro r hr
      have hr' : r ∈ Ioo a b := by simpa only [interior_Icc] using hr
      exact (hYD r hr').differentiableAt.differentiableWithinAt
    · intro r hr
      have hr' : r ∈ Ioo a b := by simpa only [interior_Icc] using hr
      rw [(hYD r hr').deriv]
      apply mul_nonneg (Real.exp_pos _).le
      have hcoef : 0 ≤ -2*(V r).re-mu^2 := by linarith [hV r hr']
      exact add_nonneg (mul_nonneg (by norm_num) (Complex.normSq_nonneg _))
        (mul_nonneg hcoef (Complex.normSq_nonneg _))
  have hG : ∀ r ∈ Icc a b, G r ≤ 0 := by
    intro r hr
    have hle := hmono hr ⟨hab,le_rfl⟩ hr.2
    have hb : Y b ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hterminal
    have hrY : Real.exp (-mu*(r-a))*G r ≤ 0 := hle.trans hb
    nlinarith [Real.exp_pos (-mu*(r-a))]
  let Z := fun r => Real.exp (mu*(r-a))*M r
  have hZc : ContinuousOn Z (Icc a b) :=
    (Real.continuous_exp.comp_continuousOn
      ((continuousOn_id.sub continuousOn_const).const_mul mu)).mul hMc
  have hZD (r : ℝ) (hr : r ∈ Ioo a b) :
      HasDerivAt Z (Real.exp (mu*(r-a))*G r) r := by
    have h := ((((hasDerivAt_id r).sub_const a).const_mul mu).exp).mul (hMD r hr)
    apply h.congr_deriv
    dsimp only [G,id_eq]
    ring
  have hanti : AntitoneOn Z (Icc a b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a b) hZc
    · intro r hr
      have hr' : r ∈ Ioo a b := by simpa only [interior_Icc] using hr
      exact (hZD r hr').differentiableAt.differentiableWithinAt
    · intro r hr
      have hr' : r ∈ Ioo a b := by simpa only [interior_Icc] using hr
      rw [(hZD r hr').deriv]
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (hG r ⟨hr'.1.le,hr'.2.le⟩)
  have hz := hanti ⟨le_rfl,hab⟩ ⟨hab,le_rfl⟩ hab
  change Real.exp (mu*(b-a))*M b ≤ Real.exp (mu*(a-a))*M a at hz
  simp only [sub_self,mul_zero,Real.exp_zero,one_mul] at hz
  have hh := mul_le_mul_of_nonneg_left hz (Real.exp_pos (-mu*(b-a))).le
  have hex : Real.exp (-mu*(b-a))*Real.exp (mu*(b-a)) = 1 := by
    rw [← Real.exp_add,show -mu*(b-a)+mu*(b-a) = 0 by ring,Real.exp_zero]
  rwa [← mul_assoc,hex,one_mul] at hh

end DefocusingNLS

end OAI
