import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialSmallInverseBoundary
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialCoupledUniqueness
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPotentialParameter

namespace OAI

/-! Quantitative parameter continuity of the actual nonlinear inner amplitude. -/

open Set
open scoped BoundedContinuousFunction
namespace DefocusingNLS

theorem radial_coupled_parameter_bound (P Q : RadialInnerData)
    (hp : Q.p=P.p) (hR : Q.R=P.R) (H K : ℝ → ℝ)
    (hH : RadialInnerOutputSpec P.p P.R P.lo P.c P.b H H)
    (hK : RadialInnerOutputSpec Q.p Q.R Q.lo Q.c Q.b K K) :
    ∀ r ∈ Icc 0 P.R, |H r-K r| ≤ 3*|P.lo-Q.lo|+|P.c-Q.c|+|P.b-Q.b| := by
  have hK' : RadialInnerOutputSpec P.p P.R Q.lo Q.c Q.b K K := by
    simpa only [hp,hR] using hK
  have hHI : ∀ r ∈ Icc 0 P.R, H r ∈ Icc (999/1000 : ℝ) 1 :=
    fun r hr => ⟨P.lo_lower.trans (hH.2.2.2.2.1 r hr).1.1,(hH.2.2.2.2.1 r hr).1.2⟩
  have hKI : ∀ r ∈ Icc 0 P.R, K r ∈ Icc (999/1000 : ℝ) 1 :=
    fun r hr => ⟨Q.lo_lower.trans (hK'.2.2.2.2.1 r hr).1.1,(hK'.2.2.2.2.1 r hr).1.2⟩
  let d : ℝ →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun r => H (radialClamp P.R r)-K (radialClamp P.R r))
    ((hH.1.continuous.comp (continuous_radialClamp P.R)).sub
      (hK'.1.continuous.comp (continuous_radialClamp P.R))) 2 (by
        intro r
        have hr := radialClamp_mem P.R r (by linarith [P.hR])
        rw [Real.norm_eq_abs]
        exact abs_le.mpr ⟨by linarith [(hHI _ hr).1,(hKI _ hr).2],
          by linarith [(hHI _ hr).2,(hKI _ hr).1]⟩)
  have hD : ∀ r ∈ Icc 0 P.R, |H r-K r| ≤ ‖d‖ := by
    intro r hr
    have hh := d.norm_coe_le_norm r
    change ‖H (radialClamp P.R r)-K (radialClamp P.R r)‖ ≤ ‖d‖ at hh
    simpa only [radialClamp_eq P.R r hr,Real.norm_eq_abs] using hh
  let V := radialAmplitudePotential P.c P.b H
  let W := radialAmplitudePotential Q.c Q.b K
  let M := 10*‖d‖+|P.c-Q.c|+|P.b-Q.b|
  let E := |P.lo-Q.lo|
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hE : 0 ≤ E := abs_nonneg _
  have hV : ∀ r ∈ Ioo 0 P.R, V r ≤ (1/2 : ℝ) := by
    intro r hr
    exact (radialAmplitudePotential_bounds P.c P.b P.R P.hc P.hb P.hR2 H hH.1.continuous
      hHI r ⟨hr.1.le,hr.2.le⟩).2
  have hW : ∀ r ∈ Ioo 0 P.R, W r ∈ Icc (3/10 : ℝ) (1/2) := by
    intro r hr
    exact radialAmplitudePotential_bounds Q.c Q.b P.R Q.hc Q.hb P.hR2 K hK'.1.continuous
      hKI r ⟨hr.1.le,hr.2.le⟩
  have hVW : ∀ r ∈ Ioo 0 P.R, |V r-W r| ≤ M := by
    intro r hr
    have hi : r ∈ Icc 0 P.R := ⟨hr.1.le,hr.2.le⟩
    have ha := radialAmplitudePotential_difference P.c P.b P.R ‖d‖ P.hc P.hR2
      (norm_nonneg _) H K hH.1.continuous hK'.1.continuous hHI hKI hD r hi
    have hb := radialAmplitudePotential_parameter_difference P.c Q.c P.b Q.b P.R
      P.hc Q.hc P.hR2 K hK'.1.continuous hKI r hi
    exact (abs_sub_le (V r) (radialAmplitudePotential P.c P.b K r) (W r)).trans (by
      dsimp [V,W,M] at *
      linarith)
  have hcoreH := radial_scalar_core_lower P.p (by have := P.hp; omega) P.R P.m P.lo
    P.hR P.hR2 P.hm P.hm1 P.hmp P.hlo H V hH.1 hH.2.1 hH.2.2.2.1.deriv hH.2.2.1
    (fun r hr => by linarith [(hHI r hr).1])
    (fun r hr => ⟨(radialAmplitudePotential_bounds P.c P.b P.R P.hc P.hb P.hR2 H
      hH.1.continuous hHI r ⟨hr.1.le,hr.2.le⟩).1,hV r hr⟩) hH.2.2.2.2.2
  have hcoreK := radial_scalar_core_lower P.p (by have := P.hp; omega) P.R P.m Q.lo
    P.hR P.hR2 P.hm P.hm1 P.hmp Q.hlo K W hK'.1 hK'.2.1 hK'.2.2.2.1.deriv hK'.2.2.1
    (fun r hr => by linarith [(hKI r hr).1]) hW hK'.2.2.2.2.2
  have hd : deriv (H-K)=fun r => deriv H r-deriv K r := by
    funext r
    exact ((hH.1 r).hasDerivAt.sub (hK'.1 r).hasDerivAt).deriv
  have hbound := radial_small_inverse_boundary_bound P.p (by have := P.hp; omega) P.R M E
    P.hR P.hR2 hM hE V (fun r => radialPowerSlope P.p (H r) (K r)) (H-K)
    (hH.1.sub hK'.1) (fun r hr => by rw [hd]; exact (hH.2.1 r hr).sub (hK'.2.1 r hr))
    (by rw [hd]; simp only [hH.2.2.2.1.deriv,hK'.2.2.2.1.deriv,sub_self])
    (by change |H P.R-K P.R| ≤ E; rw [hH.2.2.1,hK'.2.2.1]) hV
    (fun r hr => radialPowerSlope_nonneg P.p _ _
      (by linarith [(hHI r ⟨hr.1.le,hr.2.le⟩).1])
      (by linarith [(hKI r ⟨hr.1.le,hr.2.le⟩).1]))
    (fun r hr hc => by
      have hh := radialPowerSlope_lower P.p P.m (H r) (K r) (by linarith [P.hm])
        (hcoreH r ⟨hr.1.le,hr.2.le⟩ hc) (hcoreK r ⟨hr.1.le,hr.2.le⟩ hc)
      simpa only [P.hmp,mul_one_div] using hh)
    (by
      intro r hr
      rw [radial_scalar_difference_equation P.p V W H K hH.1 hK'.1 r (hH.2.1 r hr)
        (hK'.2.1 r hr) (hH.2.2.2.2.2 r hr) (hK'.2.2.2.2.2 r hr),abs_mul,
        abs_of_nonneg (by linarith [(hKI r ⟨hr.1.le,hr.2.le⟩).1] : 0 ≤ K r)]
      exact (mul_le_mul (hVW r hr) (hKI r ⟨hr.1.le,hr.2.le⟩).2
        (by linarith [(hKI r ⟨hr.1.le,hr.2.le⟩).1]) hM).trans_eq (mul_one M))
  have hsup : ‖d‖ ≤ E+(M+E/2)*(10/(P.p : ℝ)+(8/10000 : ℝ)^2) := by
    apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
    intro r
    change ‖H (radialClamp P.R r)-K (radialClamp P.R r)‖ ≤ _
    rw [Real.norm_eq_abs]
    exact hbound _ (radialClamp_mem P.R r (by linarith [P.hR]))
  have hp400 : (400 : ℝ) ≤ P.p := by exact_mod_cast P.hp
  have hθ : 10/(P.p : ℝ)+(8/10000 : ℝ)^2 ≤ (1/20 : ℝ) := by
    have hh : 10/(P.p : ℝ) ≤ (1/40 : ℝ) := (div_le_iff₀ (by linarith)).mpr (by linarith)
    linarith
  have hsup' : ‖d‖ ≤ E+(M+E/2)/20 := hsup.trans
    (add_le_add le_rfl (by
      simpa only [div_eq_mul_inv,one_mul] using mul_le_mul_of_nonneg_left hθ (by positivity : 0 ≤ M+E/2)))
  intro r hr
  apply (hD r hr).trans
  dsimp [M,E] at hsup' ⊢
  nlinarith [abs_nonneg (P.lo-Q.lo),abs_nonneg (P.c-Q.c),abs_nonneg (P.b-Q.b)]

end DefocusingNLS

end OAI
