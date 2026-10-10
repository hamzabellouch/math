import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPoissonRepresentation
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialScalarDerivativeBounds
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPotentialContinuity
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialClampedPhase
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialInnerFixedPoint
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Instances.ENNReal.Lemmas

namespace OAI

/-! Exact integral equation and uniform derivative bounds for the genuine coupled inner profiles. -/

open Set
namespace DefocusingNLS

theorem radial_inner_integral_and_continuity (P : RadialInnerData) (H : ℝ → ℝ)
    (hH : RadialInnerOutputSpec P.p P.R P.lo P.c P.b H H) :
    (∀ r ∈ Icc 0 P.R, deriv H r=r*radialAverage
      (fun t => (H t)^P.p-radialAmplitudePotential P.c P.b H t*H t) r) ∧
    ContinuousOn (deriv H) (Icc 0 P.R) := by
  let B := radialClampedAmplitude P.R H
  let f := fun r => (B r)^P.p-radialAmplitudePotential P.c P.b B r*B r
  have hB : Continuous B := radialClampedAmplitude_continuous P.R H hH.1.continuous
  have hBz : ∀ r, B r ≠ 0 := by
    intro r
    have h := (hH.2.2.2.2.1 _ (radialClamp_mem P.R r (by linarith [P.hR]))).1.1
    change H (radialClamp P.R r) ≠ 0
    linarith [P.lo_lower]
  have hf : Continuous f := (hB.pow P.p).sub
    ((continuous_radialAmplitudePotential P.c P.b B hB hBz).mul hB)
  have he : EqOn B H (Icc 0 P.R) := fun _ hr => radialClampedAmplitude_eq P.R H _ hr
  have hfe : EqOn f (fun r => (H r)^P.p-radialAmplitudePotential P.c P.b H r*H r) (Icc 0 P.R) := by
    intro r hr
    change (B r)^P.p-radialAmplitudePotential P.c P.b B r*B r= _
    rw [show B r=H r from he hr,radialAmplitudePotential_congr P.c P.b P.R B H he r hr]
  have hODE : ∀ r ∈ Ioo 0 P.R, deriv (deriv H) r+11/r*deriv H r=f r := by
    intro r hr
    rw [hfe ⟨hr.1.le,hr.2.le⟩]
    linarith [hH.2.2.2.2.2 r hr]
  have hD := radial_poisson_derivative P.R (by linarith [P.hR]) P.hR2 H f hH.1 hf hH.2.1
    hH.2.2.2.1.deriv hODE
  constructor
  · intro r hr
    rw [hD r hr]
    congr 1
    exact radialAverage_congr f _ r hr.1 (fun t ht => hfe ⟨ht.1,ht.2.trans hr.2⟩)
  · exact (continuous_id.mul (continuous_radialAverage f hf)).continuousOn.congr
      (fun r hr => hD r hr)


theorem radial_inner_integral_formula (P : RadialInnerData) (H : ℝ → ℝ)
    (hH : RadialInnerOutputSpec P.p P.R P.lo P.c P.b H H) :
    ∀ r ∈ Icc 0 P.R, deriv H r=r*radialAverage
      (fun t => (H t)^P.p-radialAmplitudePotential P.c P.b H t*H t) r :=
  (radial_inner_integral_and_continuity P H hH).1

theorem radial_inner_derivative_bounds (P : RadialInnerData) (H : ℝ → ℝ)
    (hH : RadialInnerOutputSpec P.p P.R P.lo P.c P.b H H) :
    (∀ r ∈ Icc 0 P.R, ‖deriv H r‖ ≤ r/24) ∧
    (∀ r ∈ Ioo 0 P.R, ‖deriv (deriv H) r‖ ≤ (23/24 : ℝ)) := by
  have hHI : ∀ r ∈ Icc 0 P.R, H r ∈ Icc 0 1 := by
    intro r hr
    have h := (hH.2.2.2.2.1 r hr).1
    exact ⟨by linarith [h.1,P.lo_lower],h.2⟩
  have hV : ∀ r ∈ Icc 0 P.R, radialAmplitudePotential P.c P.b H r ∈ Icc (3/10 : ℝ) (1/2) := by
    intro r hr
    exact radialAmplitudePotential_bounds P.c P.b P.R P.hc P.hb P.hR2 H hH.1.continuous
      (fun t ht => ⟨P.lo_lower.trans (hH.2.2.2.2.1 t ht).1.1,(hH.2.2.2.2.1 t ht).1.2⟩) r hr
  have hp : 1 ≤ P.p := by have := P.hp; omega
  have hInt := radial_inner_integral_formula P H hH
  exact ⟨radial_scalar_first_derivative_bound P.p hp P.R H (radialAmplitudePotential P.c P.b H)
      hHI (fun r hr => (hH.2.2.2.2.1 r hr).2) hV hInt,
    radial_scalar_second_derivative_bound P.p hp P.R H (radialAmplitudePotential P.c P.b H)
      hHI (fun r hr => (hH.2.2.2.2.1 r hr).2) hV hInt hH.2.2.2.2.2⟩

theorem radial_inner_derivative_lipschitz (P : RadialInnerData) (H : ℝ → ℝ)
    (hH : RadialInnerOutputSpec P.p P.R P.lo P.c P.b H H) :
    LipschitzOnWith 1 (deriv H) (Icc 0 P.R) := by
  have hL : LipschitzOnWith 1 (deriv H) (Ioo 0 P.R) :=
    (convex_Ioo (0 : ℝ) P.R).lipschitzOnWith_of_nnnorm_deriv_le hH.2.1 (by
      intro r hr
      change ‖deriv (deriv H) r‖₊ ≤ (1 : NNReal)
      exact_mod_cast ((radial_inner_derivative_bounds P H hH).2 r hr).trans (by norm_num))
  have hc : ContinuousOn (deriv H) (closure (Ioo 0 P.R)) := by
    rw [closure_Ioo (by linarith [P.hR] : (0 : ℝ) ≠ P.R)]
    exact (radial_inner_integral_and_continuity P H hH).2
  have h := LipschitzOnWith.closure hc hL
  rwa [closure_Ioo (by linarith [P.hR] : (0 : ℝ) ≠ P.R)] at h

end DefocusingNLS

end OAI
