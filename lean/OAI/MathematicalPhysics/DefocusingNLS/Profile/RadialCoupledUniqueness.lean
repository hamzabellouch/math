import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialInnerFixedPoint

namespace OAI

/-! Uniqueness in the proved positive-amplitude class for the coupled inner problem. -/

open Set
open scoped BoundedContinuousFunction
namespace DefocusingNLS

theorem radial_coupled_profile_unique (P : RadialInnerData) (H K : ℝ → ℝ)
    (hH : RadialInnerOutputSpec P.p P.R P.lo P.c P.b H H)
    (hK : RadialInnerOutputSpec P.p P.R P.lo P.c P.b K K) : EqOn H K (Icc 0 P.R) := by
  let d : ℝ →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun r => H (radialClamp P.R r)-K (radialClamp P.R r))
    ((hH.1.continuous.comp (continuous_radialClamp P.R)).sub
      (hK.1.continuous.comp (continuous_radialClamp P.R))) 2 (by
        intro r
        have hr := radialClamp_mem P.R r (by linarith [P.hR])
        have hHI := (hH.2.2.2.2.1 _ hr).1
        have hKI := (hK.2.2.2.2.1 _ hr).1
        rw [Real.norm_eq_abs]
        exact abs_le.2 ⟨by linarith [P.lo_lower,hHI.1,hHI.2,hKI.1,hKI.2],by linarith [P.lo_lower,hHI.1,hHI.2,hKI.1,hKI.2]⟩)
  have hHK : ∀ r ∈ Icc 0 P.R, |H r-K r| ≤ ‖d‖ := by
    intro r hr
    have h := d.norm_coe_le_norm r
    change ‖H (radialClamp P.R r)-K (radialClamp P.R r)‖ ≤ ‖d‖ at h
    simpa only [radialClamp_eq P.R r hr,Real.norm_eq_abs] using h
  have hC := radial_inner_output_contraction P.p (by have := P.hp; omega)
    P.R P.lo P.c P.b P.m ‖d‖ P.hR P.hR2 P.hlo P.hm P.hm1 P.hmp P.hc P.hb
    (norm_nonneg _) H K H K hH.1.continuous hK.1.continuous
    (fun r hr => ⟨P.lo_lower.trans (hH.2.2.2.2.1 r hr).1.1,(hH.2.2.2.2.1 r hr).1.2⟩)
    (fun r hr => ⟨P.lo_lower.trans (hK.2.2.2.2.1 r hr).1.1,(hK.2.2.2.2.1 r hr).1.2⟩) hHK hH hK
  have hn : ‖d‖ ≤ (1/2 : ℝ)*‖d‖ := by
    apply (BoundedContinuousFunction.norm_le (by positivity)).2
    intro r
    change ‖H (radialClamp P.R r)-K (radialClamp P.R r)‖ ≤ _
    rw [Real.norm_eq_abs]
    exact (hC _ (radialClamp_mem P.R r (by linarith [P.hR]))).trans
      (mul_le_mul_of_nonneg_right (radial_inner_contraction_constant P.p P.hp) (norm_nonneg _))
  have hz : ‖d‖=0 := by linarith [norm_nonneg d]
  intro r hr
  have h := hHK r hr
  rw [hz] at h
  exact sub_eq_zero.1 (abs_nonpos_iff.1 h)

end DefocusingNLS

end OAI
