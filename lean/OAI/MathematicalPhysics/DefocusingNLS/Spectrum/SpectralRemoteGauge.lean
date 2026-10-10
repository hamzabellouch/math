import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteReductionStep
import Mathlib.Analysis.Calculus.FDeriv.Mul

namespace OAI

/-! The near-identity reduction is an exact change of variables for the
four-coordinate differential equation. -/

open Filter Topology
namespace DefocusingNLS

theorem spectralRemote_operator_apply (A : ℝ → SpectralRemoteOperator)
    (A' : SpectralRemoteOperator) (u : ℝ → SpectralRemoteSpace)
    (u' : SpectralRemoteSpace) (t : ℝ)
    (hA : HasDerivAt A A' t) (hu : HasDerivAt u u' t) :
    HasDerivAt (fun s => A s (u s)) (A' (u t)+A t u') t := by
  have har := (ContinuousLinearMap.restrictScalarsL ℂ SpectralRemoteSpace SpectralRemoteSpace ℝ ℝ).hasFDerivAt.comp_hasDerivAt t hA
  simpa only [ContinuousLinearMap.coe_restrict_scalarsL',Function.comp_def,
    ContinuousLinearMap.coe_restrictScalars'] using har.clm_apply hu

noncomputable def spectralRemoteGauge (S : ℝ → SpectralRemoteOperator)
    (Y : ℝ → SpectralRemoteSpace) (t : ℝ) : SpectralRemoteSpace :=
  Ring.inverse (1+S t) (Y t)

theorem spectralRemote_gauge_hasDerivAt (S : ℝ → SpectralRemoteOperator)
    (Y : ℝ → SpectralRemoteSpace) (t : ℝ) (L B B₀ dS : SpectralRemoteOperator)
    (hS : HasDerivAt S dS t) (hsmall : ‖S t‖ ≤ 1/2)
    (hY : HasDerivAt Y ((L+B) (Y t)) t) :
    HasDerivAt (spectralRemoteGauge S Y)
      ((L+B₀+spectralRemoteReducedRemainder L B B₀ (S t) dS)
        (spectralRemoteGauge S Y t)) t := by
  let T := fun s => (1 : SpectralRemoteOperator)+S s
  let Z := spectralRemoteGauge S Y
  have hT : HasDerivAt T dS t := by
    simpa only [T] using hS.const_add (1 : SpectralRemoteOperator)
  have hunit : IsUnit (T t) := (spectralRemote_near_identity_inverse (S t) hsmall).1
  have hi : DifferentiableAt ℝ (fun s => Ring.inverse (T s)) t :=
    (differentiableAt_inverse (𝕜 := ℝ) hunit).comp t hT.differentiableAt
  have hZ : DifferentiableAt ℝ Z t :=
    (spectralRemote_operator_apply _ _ _ _ t hi.hasDerivAt hY).differentiableAt
  have hu : ∀ᶠ s in 𝓝 t, IsUnit (T s) :=
    hT.continuousAt.eventually (Units.isOpen.mem_nhds hunit)
  have hTZ : (fun s => T s (Z s)) =ᶠ[𝓝 t] Y := by
    filter_upwards [hu] with s hs
    change (T s*Ring.inverse (T s)) (Y s) = Y s
    rw [Ring.mul_inverse_cancel _ hs]
    rfl
  have hTZt : T t (Z t) = Y t := hTZ.eq_of_nhds
  have hd := (spectralRemote_operator_apply _ _ _ _ t hT hZ.hasDerivAt).congr_of_eventuallyEq hTZ.symm
  have he := hd.unique hY
  have hrel : T t (deriv Z t) = (L+B) (Y t)-dS (Z t) := by
    change dS (Z t)+T t (deriv Z t) = (L+B) (Y t) at he
    exact eq_sub_of_add_eq (by simpa only [add_comm] using he)
  have hz : deriv Z t =
      (Ring.inverse (T t)*((L+B)*T t-dS)) (Z t) := by
    calc
      deriv Z t = Ring.inverse (T t) (T t (deriv Z t)) := by
        change deriv Z t = (Ring.inverse (T t)*T t) (deriv Z t)
        rw [Ring.inverse_mul_cancel _ hunit]
        rfl
      _ = Ring.inverse (T t) ((L+B) (T t (Z t))-dS (Z t)) := by rw [hrel,hTZt]
      _ = _ := by simp only [mul_apply_eq_comp,sub_apply]
  apply hZ.hasDerivAt.congr_deriv
  rw [hz]
  congr 1
  dsimp only [spectralRemoteReducedRemainder,T]
  abel

end DefocusingNLS

end OAI
