import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialInnerMap
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialScalarCore
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialScalarDifference
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPotentialDifference

namespace OAI

/-! Canonical scalar outputs and their contraction estimate for the actual inner potential. -/

open Set
open scoped BoundedContinuousFunction
namespace DefocusingNLS

def RadialInnerOutputSpec (p : ℕ) (R lo c b : ℝ) (A H : ℝ → ℝ) : Prop :=
  Differentiable ℝ H ∧
  (∀ r ∈ Ioo 0 R, DifferentiableAt ℝ (deriv H) r) ∧
  H R=lo ∧ HasDerivAt H 0 0 ∧
  (∀ r ∈ Icc 0 R, H r ∈ Icc lo 1 ∧ (H r)^(p-1) ≤ (1/2 : ℝ)) ∧
  (∀ r ∈ Ioo 0 R, -deriv (deriv H) r-11/r*deriv H r+(H r)^p=
    radialAmplitudePotential c b A r*H r)

theorem exists_radial_inner_output_spec (p : ℕ) (hp : 2 ≤ p) (R lo c b : ℝ)
    (hR : 0 < R) (hR2 : R^2 ≤ 11) (hlo : (999/1000 : ℝ) ≤ lo)
    (hSmall : lo^(p-1) ≤ (3/10 : ℝ))
    (hc : c ∈ Icc (599/100 : ℝ) 6) (hb : b ∈ Icc (334/1000 : ℝ) (335/1000))
    (A : ℝ → ℝ) (hA : Continuous A) (hAI : ∀ r, A r ∈ Icc lo 1) :
    ∃ H : ℝ → ℝ, RadialInnerOutputSpec p R lo c b A H := by
  obtain ⟨H,hH,hDH,hHR,hH0,hHI,hHE⟩ := exists_radial_inner_output p hp R lo c b
    hR hR2 hlo hSmall hc hb A hA hAI
  refine ⟨H,hH,hDH,hHR,hH0,?_,hHE⟩
  intro r hr
  have h := hHI r hr
  have h1 : H r ≤ 1 := by
    by_contra! hgt
    have hpow : 1 ≤ (H r)^(p-1) := one_le_pow₀ hgt.le
    linarith
  exact ⟨⟨h.1,h1⟩,h.2⟩

theorem radial_inner_output_contraction (p : ℕ) (hp : 10 ≤ p) (R lo c b m D : ℝ)
    (hR : 1 ≤ R) (hR2 : R^2 ≤ 11) (hlo : 1-(1/10000 : ℝ)^2/5 ≤ lo)
    (hm : (999/1000 : ℝ) ≤ m) (hm1 : m ≤ 1) (hmp : m^(p-1)=(1/5 : ℝ))
    (hc : c ∈ Icc (599/100 : ℝ) 6) (hb : b ∈ Icc (334/1000 : ℝ) (335/1000))
    (hD : 0 ≤ D) (A B H K : ℝ → ℝ) (hA : Continuous A) (hB : Continuous B)
    (hAI : ∀ r ∈ Icc 0 R, A r ∈ Icc (999/1000 : ℝ) 1)
    (hBI : ∀ r ∈ Icc 0 R, B r ∈ Icc (999/1000 : ℝ) 1)
    (hAB : ∀ r ∈ Icc 0 R, |A r-B r| ≤ D)
    (hH : RadialInnerOutputSpec p R lo c b A H)
    (hK : RadialInnerOutputSpec p R lo c b B K) :
    ∀ r ∈ Icc 0 R, |H r-K r| ≤ (10*(10/(p : ℝ)+(8/10000 : ℝ)^2))*D := by
  have hlo0 : 0 ≤ lo := by linarith
  have hHV : ∀ r ∈ Ioo 0 R, radialAmplitudePotential c b A r ∈ Icc (3/10 : ℝ) (1/2) :=
    fun r hr => radialAmplitudePotential_bounds c b R hc hb hR2 A hA hAI r ⟨hr.1.le,hr.2.le⟩
  have hKV : ∀ r ∈ Ioo 0 R, radialAmplitudePotential c b B r ∈ Icc (3/10 : ℝ) (1/2) :=
    fun r hr => radialAmplitudePotential_bounds c b R hc hb hR2 B hB hBI r ⟨hr.1.le,hr.2.le⟩
  have hHN : ∀ r ∈ Icc 0 R, 0 ≤ H r := fun r hr => hlo0.trans (hH.2.2.2.2.1 r hr).1.1
  have hKN : ∀ r ∈ Icc 0 R, 0 ≤ K r := fun r hr => hlo0.trans (hK.2.2.2.2.1 r hr).1.1
  have hHC := radial_scalar_core_lower p (by omega) R m lo hR hR2 hm hm1 hmp hlo
    H (radialAmplitudePotential c b A) hH.1 hH.2.1 hH.2.2.2.1.deriv hH.2.2.1 hHN hHV hH.2.2.2.2.2
  have hKC := radial_scalar_core_lower p (by omega) R m lo hR hR2 hm hm1 hmp hlo
    K (radialAmplitudePotential c b B) hK.1 hK.2.1 hK.2.2.2.1.deriv hK.2.2.1 hKN hKV hK.2.2.2.2.2
  have h := radial_scalar_difference_bound p hp R m (10*D) hR hR2 (by positivity)
    (by linarith) hmp (radialAmplitudePotential c b A) (radialAmplitudePotential c b B)
    H K hH.1 hK.1 hH.2.1 hK.2.1 hH.2.2.2.1.deriv hK.2.2.2.1.deriv
    (hH.2.2.1.trans hK.2.2.1.symm) hHN
    (fun r hr => ⟨hKN r hr,(hK.2.2.2.2.1 r hr).1.2⟩) hHC hKC
    (fun r hr => (hHV r hr).2)
    (fun r hr => radialAmplitudePotential_difference c b R D hc hR2 hD A B hA hB hAI hBI hAB r ⟨hr.1.le,hr.2.le⟩)
    hH.2.2.2.2.2 hK.2.2.2.2.2
  intro r hr
  exact (h r hr).trans_eq (by ring)

theorem radial_inner_contraction_constant (p : ℕ) (hp : 400 ≤ p) :
    10*(10/(p : ℝ)+(8/10000 : ℝ)^2) ≤ (1/2 : ℝ) := by
  have hpR : (400 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have h : 10/(p : ℝ) ≤ (1/40 : ℝ) := (div_le_iff₀ hp0).2 (by linarith)
  linarith

end DefocusingNLS

end OAI
