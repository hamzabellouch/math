import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialScalarProfile
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialScalarComparison
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialVelocityBounds

namespace OAI

/-! The scalar output exists for the actual amplitude-dependent inner potential. -/

open Set
namespace DefocusingNLS

theorem exists_radial_inner_output (p : ℕ) (hp : 2 ≤ p) (R lo c b : ℝ)
    (hR : 0 < R) (hR2 : R^2 ≤ 11) (hlo : (999/1000 : ℝ) ≤ lo)
    (hSmall : lo^(p-1) ≤ (3/10 : ℝ))
    (hc : c ∈ Icc (599/100 : ℝ) 6) (hb : b ∈ Icc (334/1000 : ℝ) (335/1000))
    (A : ℝ → ℝ) (hA : Continuous A) (hAI : ∀ r, A r ∈ Icc lo 1) :
    ∃ H : ℝ → ℝ, Differentiable ℝ H ∧
      (∀ r ∈ Ioo 0 R, DifferentiableAt ℝ (deriv H) r) ∧
      H R=lo ∧ HasDerivAt H 0 0 ∧
      (∀ r ∈ Icc 0 R, lo ≤ H r ∧ (H r)^(p-1) ≤ (1/2 : ℝ)) ∧
      (∀ r ∈ Ioo 0 R,
        -deriv (deriv H) r-11/r*deriv H r+(H r)^p=
          radialAmplitudePotential c b A r*H r) := by
  have hAP (r : ℝ) : 0 < A r := lt_of_lt_of_le
    (by norm_num : (0 : ℝ) < 999/1000) (hlo.trans (hAI r).1)
  have hρ : Continuous (radialVelocityRatio c A) := by
    exact (continuous_const.mul (continuous_radialAverage (fun t => (A t)^2) (hA.pow 2))).div
      (hA.pow 2) (fun r => pow_ne_zero 2 (hAP r).ne')
  have hPot : Continuous (radialAmplitudePotential c b A) := by
    unfold radialAmplitudePotential
    exact continuous_const.add ((continuous_id.pow 2).div_const 16) |>.sub
      (((continuous_id.pow 2).mul (hρ.pow 2)).div_const 4)
  let V := fun r => radialAmplitudePotential c b A (radialClamp R r)
  have hV : Continuous V := hPot.comp (continuous_radialClamp R)
  have hVB : ∀ r ∈ Icc 0 R, V r ∈ Icc (3/10 : ℝ) (1/2) := by
    intro r hr
    change radialAmplitudePotential c b A (radialClamp R r) ∈ _
    rw [radialClamp_eq R r hr]
    exact radialAmplitudePotential_bounds c b R hc hb hR2 A hA
      (fun s _ => ⟨hlo.trans (hAI s).1,(hAI s).2⟩) r hr
  obtain ⟨H,hH,hD,hHR,hH0,hHI,hEq⟩ := exists_radial_scalar_profile_regular p hp R lo hR
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 999/1000) hlo) hSmall V hV hVB
  refine ⟨H,hH,hD,hHR,hH0,hHI,?_⟩
  intro r hr
  have h := hEq r hr
  change -deriv (deriv H) r-11/r*deriv H r+(H r)^p=
    radialAmplitudePotential c b A (radialClamp R r)*H r at h
  rwa [radialClamp_eq R r ⟨hr.1.le,hr.2.le⟩] at h

end DefocusingNLS

end OAI
