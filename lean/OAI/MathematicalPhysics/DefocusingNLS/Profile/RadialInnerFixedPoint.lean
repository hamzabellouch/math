import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialInnerOutput
import Mathlib.Topology.MetricSpace.Contracting

namespace OAI

/-! A genuine fixed point of the coupled inner amplitude equation. -/

open Set
open scoped BoundedContinuousFunction
namespace DefocusingNLS

/-- Only numerical parameter conditions; no analytic conclusion is part of the data. -/
structure RadialInnerData where
  p : ℕ
  R : ℝ
  lo : ℝ
  c : ℝ
  b : ℝ
  m : ℝ
  hp : 400 ≤ p
  hR : 1 ≤ R
  hR2 : R^2 ≤ 11
  hlo : 1-(1/10000 : ℝ)^2/5 ≤ lo
  hlo1 : lo ≤ 1
  hSmall : lo^(p-1) ≤ (3/10 : ℝ)
  hm : (999/1000 : ℝ) ≤ m
  hm1 : m ≤ 1
  hmp : m^(p-1)=(1/5 : ℝ)
  hc : c ∈ Icc (599/100 : ℝ) 6
  hb : b ∈ Icc (334/1000 : ℝ) (335/1000)

theorem RadialInnerData.lo_lower (P : RadialInnerData) : (999/1000 : ℝ) ≤ P.lo := by
  linarith [P.hlo]

noncomputable def radialInnerClampedInput (P : RadialInnerData) (A : ℝ →ᵇ ℝ) : ℝ → ℝ :=
  fun r => radialAmplitudeClamp P.lo 1 (A r)

theorem radialInnerClampedInput_continuous (P : RadialInnerData) (A : ℝ →ᵇ ℝ) :
    Continuous (radialInnerClampedInput P A) :=
  (radialAmplitudeClamp_lipschitz P.lo 1).continuous.comp A.continuous

theorem radialInnerClampedInput_mem (P : RadialInnerData) (A : ℝ →ᵇ ℝ) (r : ℝ) :
    radialInnerClampedInput P A r ∈ Icc P.lo 1 :=
  radialAmplitudeClamp_mem P.lo 1 (A r) P.hlo1

noncomputable def radialInnerRaw (P : RadialInnerData) (A : ℝ →ᵇ ℝ) : ℝ → ℝ :=
  Classical.choose (exists_radial_inner_output_spec P.p (by have := P.hp; omega)
    P.R P.lo P.c P.b (by linarith [P.hR]) P.hR2 P.lo_lower P.hSmall P.hc P.hb
    (radialInnerClampedInput P A) (radialInnerClampedInput_continuous P A)
    (radialInnerClampedInput_mem P A))

theorem radialInnerRaw_spec (P : RadialInnerData) (A : ℝ →ᵇ ℝ) :
    RadialInnerOutputSpec P.p P.R P.lo P.c P.b (radialInnerClampedInput P A) (radialInnerRaw P A) :=
  Classical.choose_spec (exists_radial_inner_output_spec P.p (by have := P.hp; omega)
    P.R P.lo P.c P.b (by linarith [P.hR]) P.hR2 P.lo_lower P.hSmall P.hc P.hb
    (radialInnerClampedInput P A) (radialInnerClampedInput_continuous P A)
    (radialInnerClampedInput_mem P A))

noncomputable def radialInnerOperator (P : RadialInnerData) (A : ℝ →ᵇ ℝ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun r => radialInnerRaw P A (radialClamp P.R r))
    ((radialInnerRaw_spec P A).1.continuous.comp (continuous_radialClamp P.R)) 1 (by
      intro r
      have hr := radialClamp_mem P.R r (by linarith [P.hR])
      have h := ((radialInnerRaw_spec P A).2.2.2.2.1 _ hr).1
      rw [Real.norm_eq_abs,abs_of_nonneg (by linarith [P.lo_lower,h.1])]
      exact h.2)

theorem radialInnerOperator_contracting (P : RadialInnerData) :
    ContractingWith ⟨1/2,by norm_num⟩ (radialInnerOperator P) := by
  refine ⟨by change (1/2 : ℝ) < 1; norm_num,LipschitzWith.of_dist_le_mul ?_⟩
  intro A B
  rw [dist_eq_norm,dist_eq_norm]
  change ‖radialInnerOperator P A-radialInnerOperator P B‖ ≤ (1/2 : ℝ)*‖A-B‖
  have hAB : ∀ r ∈ Icc 0 P.R,
      |radialInnerClampedInput P A r-radialInnerClampedInput P B r| ≤ ‖A-B‖ := by
    intro r _
    have h := (radialAmplitudeClamp_lipschitz P.lo 1).dist_le_mul (A r) (B r)
    rw [dist_eq_norm,dist_eq_norm,NNReal.coe_one,one_mul] at h
    exact (Real.norm_eq_abs _ ▸ h).trans ((A-B).norm_coe_le_norm r)
  have h := radial_inner_output_contraction P.p (by have := P.hp; omega)
    P.R P.lo P.c P.b P.m ‖A-B‖ P.hR P.hR2 P.hlo P.hm P.hm1 P.hmp P.hc P.hb
    (norm_nonneg _) _ _ _ _ (radialInnerClampedInput_continuous P A)
    (radialInnerClampedInput_continuous P B)
    (fun r _ => ⟨P.lo_lower.trans (radialInnerClampedInput_mem P A r).1,
      (radialInnerClampedInput_mem P A r).2⟩)
    (fun r _ => ⟨P.lo_lower.trans (radialInnerClampedInput_mem P B r).1,
      (radialInnerClampedInput_mem P B r).2⟩) hAB (radialInnerRaw_spec P A) (radialInnerRaw_spec P B)
  apply (BoundedContinuousFunction.norm_le (by positivity)).2
  intro r
  change ‖radialInnerRaw P A (radialClamp P.R r)-radialInnerRaw P B (radialClamp P.R r)‖ ≤ _
  rw [Real.norm_eq_abs]
  exact (h _ (radialClamp_mem P.R r (by linarith [P.hR]))).trans
    (mul_le_mul_of_nonneg_right (radial_inner_contraction_constant P.p P.hp) (norm_nonneg _))

theorem exists_radial_coupled_profile (P : RadialInnerData) :
    ∃ H : ℝ → ℝ, Differentiable ℝ H ∧
      (∀ r ∈ Ioo 0 P.R, DifferentiableAt ℝ (deriv H) r) ∧
      H P.R=P.lo ∧ HasDerivAt H 0 0 ∧
      (∀ r ∈ Icc 0 P.R, H r ∈ Icc P.lo 1 ∧ (H r)^(P.p-1) ≤ (1/2 : ℝ)) ∧
      (∀ r ∈ Ioo 0 P.R,
        -deriv (deriv H) r-11/r*deriv H r+(H r)^P.p=
          radialAmplitudePotential P.c P.b H r*H r) := by
  let A := (radialInnerOperator_contracting P).fixedPoint (radialInnerOperator P)
  let H := radialInnerRaw P A
  have hH := radialInnerRaw_spec P A
  have hFix : radialInnerOperator P A=A := (radialInnerOperator_contracting P).fixedPoint_isFixedPt
  have hAH : EqOn (fun r => A r) H (Icc 0 P.R) := by
    intro r hr
    have h := congrArg (fun f : ℝ →ᵇ ℝ => f r) hFix
    change radialInnerRaw P A (radialClamp P.R r)=A r at h
    rw [radialClamp_eq P.R r hr] at h
    exact h.symm
  have hCH : EqOn (radialInnerClampedInput P A) H (Icc 0 P.R) := by
    intro r hr
    change radialAmplitudeClamp P.lo 1 (A r)=H r
    have hrEq : A r=H r := hAH hr
    rw [hrEq]
    exact radialAmplitudeClamp_eq P.lo 1 (H r) (hH.2.2.2.2.1 r hr).1
  refine ⟨H,hH.1,hH.2.1,hH.2.2.1,hH.2.2.2.1,hH.2.2.2.2.1,?_⟩
  intro r hr
  have he := hH.2.2.2.2.2 r hr
  rw [radialAmplitudePotential_congr P.c P.b P.R (radialInnerClampedInput P A) H hCH r
    ⟨hr.1.le,hr.2.le⟩] at he
  exact he

end DefocusingNLS

end OAI
