import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.ExpandingArrayLoss
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.ParabolicComparison
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.ScalarMass
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.SmoothProfilesIntegrableImpulse

namespace OAI

noncomputable section
namespace VelocityDetection.ExpandingArray
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open Stacks SmoothProfiles
open scoped ZeroAtInfty
variable {N b : ℕ} (hb : 0 < b) (table : Fin N → Fin b → Option (Rule (Fin N) b))
    (terminal : Fin N) (ν : ℝ) (m : ℕ)

theorem compactSupport_field_component (hν : 0 < ν) {t : ℝ} (ht : 0 ≤ t) (i : Fin 2) :
    HasCompactSupport (fun X => field hb table terminal ν m t X i) := by
  obtain ⟨K, hK, hzero⟩ := finiteCylinderSupport hb table terminal ν m hν t
  apply HasCompactSupport.of_support_subset_isCompact hK
  intro X hX
  by_contra hnot
  exact hX (congrFun (hzero t ht le_rfl X hnot) i)

theorem scalar_mass (hν : 0 < ν) (p : Coord 2) {ρ : ScalarField 2}
    {r dr : ℝ → Lp ℝ 1 (volume : Measure (Coord 2))}
    (hρ : ContDiff ℝ 2 (uncurry ρ))
    (hi : ∀ t, 0 ≤ t → ∀ i, Integrable (SpatialCalculus.partialD i (ρ t)))
    (hii : ∀ t, 0 ≤ t → ∀ i,
      Integrable (SpatialCalculus.partialD i (SpatialCalculus.partialD i (ρ t))))
    (heq : ∀ t, 0 ≤ t → ∀ X,
      deriv (fun s => ρ s X) t + advection (field hb table terminal ν m) ρ t X =
        ν * laplacian ρ t X + impulse p t X)
    (hrep : ∀ t, (fun X => r t X) =ᵐ[volume] ρ t)
    (hdrep : ∀ t, 0 ≤ t → (fun X => dr t X) =ᵐ[volume] (fun X => deriv (fun s => ρ s X) t))
    (hr : ∀ t, 0 ≤ t → HasDerivWithinAt r (dr t) (Ici 0) t)
    (hzero : ∀ X, ρ 0 X = 0) : ∀ t, 0 ≤ t → (∫ X, ρ t X) = step t := by
  refine ScalarMass.mass_eq_primitive hρ hi hii (fun t _ => integrable_impulse p t)
    (fun t _ i => field_slice_component hb table terminal ν m hν t i)
    (fun t ht i => compactSupport_field_component hb table terminal ν m hν ht i)
    (fun t _ X => divergence_field hb table terminal ν m hν t X)
    heq hrep hdrep hr ?_ ?_
  · intro t _
    rw [integral_impulse]
    exact (differentiable_step t).hasDerivAt.hasDerivWithinAt
  · simp only [hzero, integral_zero]
    exact Real.smoothTransition.zero.symm

theorem scalar_detection_of_tail_regular (c₀ : Configuration (Fin N))
    (hν : 0 < ν) (ρ : ℝ → C₀(Coord 2, ℝ))
    {r dr : ℝ → Lp ℝ 1 (volume : Measure (Coord 2))}
    (hρc : ContinuousOn ρ (Ici 0))
    (hρ : ContDiff ℝ 2 (fun q : ℝ × Coord 2 => ρ q.1 q.2))
    (hi : ∀ t, 0 ≤ t → ∀ i, Integrable (SpatialCalculus.partialD i (fun X => ρ t X)))
    (hii : ∀ t, 0 ≤ t → ∀ i, Integrable
      (SpatialCalculus.partialD i (SpatialCalculus.partialD i (fun X => ρ t X))))
    (heq : ∀ t, 0 ≤ t → ∀ X,
      deriv (fun s => ρ s X) t + advection (field hb table terminal ν m) (fun s Y => ρ s Y) t X =
        ν * laplacian (fun s Y => ρ s Y) t X + impulse (point hb table terminal ν m c₀ 0) t X)
    (hrep : ∀ t, (fun X => r t X) =ᵐ[volume] (fun X => ρ t X))
    (hdrep : ∀ t, 0 ≤ t → (fun X => dr t X) =ᵐ[volume] (fun X => deriv (fun s => ρ s X) t))
    (hr : ∀ t, 0 ≤ t → HasDerivWithinAt r (dr t) (Ici 0) t)
    (hzero : ∀ X, ρ 0 X = 0) (hm : 1 ≤ m)
    (hc₀ : c₀.leftStack < capacity b m 0 ∧ c₀.rightStack < capacity b m 0)
    (hdir : IncomingDirection table) (hin : IncomingRule table)
    (hterm : NoOutgoing table terminal) (hcont : Continues hb table terminal c₀)
    (hinit : c₀.state ≠ terminal) :
    Observation.planeEvent (liftVelocity (field hb table terminal ν m) (fun s Y => ρ s Y)) ↔
      Reaches hb table terminal c₀ := by
  have hp := ParabolicComparison.nonnegative_of_continuous_C0 ρ hν.le hρc hρ heq
    (fun X => (hzero X).ge)
    (fun t _ X => impulse_nonneg (point hb table terminal ν m c₀ 0) X t)
  have hmass := scalar_mass (ρ := fun t X => ρ t X) hb table terminal ν m hν (point hb table terminal ν m c₀ 0)
    hρ hi hii heq hrep hdrep hr hzero
  exact scalar_detection (ρ := fun t X => ρ t X) hb table terminal ν m c₀ hν hρ heq hzero
    (fun t _ => ScalarMass.integrable_of_L1_rep (hrep t)) hp hmass hm hc₀ hdir hin hterm hcont hinit

end VelocityDetection.ExpandingArray
end

end OAI
