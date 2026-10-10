import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialClampedPhase
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialLimitUniqueness

namespace OAI

/-! Exact plateau potential and derivative identities, including both endpoints. -/

open Set
namespace DefocusingNLS

theorem radial_potential_on_plateau (l b : ℝ) (A : ℝ → ℝ)
    (hA : EqOn A (fun _ => 1) (Icc 0 l)) :
    EqOn (radialAmplitudePotential 6 b A) (fun _ => b) (Icc 0 l) := by
  intro r hr
  have hAr : A r=1 := hA hr
  have hav : radialAverage (fun t => (A t)^2) r=1/12 := by
    rw [radialAverage_congr _ (fun _ => (1 : ℝ)) r hr.1 (by
      intro t ht
      change (A t)^2=1
      rw [show A t=1 from hA ⟨ht.1,ht.2.trans hr.2⟩]
      norm_num),radialAverage_const]
  dsimp [radialAmplitudePotential,radialVelocityRatio]
  rw [hAr,hav]
  ring

theorem radial_plateau_derivative_zero (l : ℝ) (hl : 0 < l) (A D : ℝ → ℝ)
    (hD : Continuous D) (hA : EqOn A (fun _ => 1) (Icc 0 l))
    (hAD : ∀ r ∈ Ioo 0 l, HasDerivAt A (D r) r) : EqOn D (fun _ => 0) (Icc 0 l) :=
  radial_derivative_limit_unique l hl A (fun _ => 1) D (fun _ => 0) hD continuous_const hA hAD
    (fun r _ => hasDerivAt_const r (1 : ℝ))

end DefocusingNLS

end OAI
