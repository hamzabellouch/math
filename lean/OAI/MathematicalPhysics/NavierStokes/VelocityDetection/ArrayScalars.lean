import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.ExpandingArrayForce
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.ArrayMass
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.ExpandingArrayLocalSupportField
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.TailSpaceToC0
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.JointCalculusTimeDEqDeriv

namespace OAI

noncomputable section
namespace VelocityDetection.ExpandingArray
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty
open Stacks TailSpace SmoothProfiles
variable {N b : ℕ} (hb : 0 < b) (table : Fin N → Fin b → Option (Rule (Fin N) b))
    (terminal : Fin N) (ν : ℝ) (m : ℕ)

theorem scalar_properties_of_C1Tails (hν : 0 < ν) (p : Coord 2) {ρ : ScalarField 2}
    (hρ : ContDiff ℝ ∞ (uncurry ρ)) (hr : C1Tails ρ)
    (hD : ∀ i, ContinuousTails (spatialD i ρ))
    (hDD : ∀ i k, ContinuousTails (spatialD k (spatialD i ρ)))
    (heq : ∀ t ≥ 0, ∀ X, timeD ρ t X + advection (field hb table terminal ν m) ρ t X =
      ν * laplacian ρ t X + impulse p t X)
    (hzero : ∀ X, ρ 0 X = 0) :
    (∀ t ≥ 0, ∀ X, 0 ≤ ρ t X) ∧ (∀ t, Integrable (ρ t)) ∧
      (∀ t ≥ 0, (∫ X, ρ t X) = step t) := by
  have hd (t : ℝ) (ht : 0 ≤ t) (X : Coord 2) : timeD ρ t X = deriv (fun s => ρ s X) t :=
    JointCalculus.timeD_eq_deriv ht X (hρ.differentiable (by simp) (t, X))
  have heq' (t : ℝ) (ht : 0 ≤ t) (X : Coord 2) :
      deriv (fun s => ρ s X) t + advection (field hb table terminal ν m) ρ t X =
        ν * laplacian ρ t X + impulse p t X := by
    rw [← hd t ht X]
    exact heq t ht X
  obtain ⟨F, hFc, hFr⟩ := hr.continuous.C0_rep
  have hF2 : ContDiff ℝ 2 (fun q : ℝ × Coord 2 => F q.1 q.2) := by
    simpa only [hFr, Function.uncurry_def] using hρ.of_le (show (2 : ℕ∞ω) ≤ ∞ by exact WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hp := ParabolicComparison.nonnegative_of_continuous_C0 F hν.le hFc hF2
    (by simpa only [hFr] using heq') (fun X => by simpa only [hFr, hzero] using (le_refl (0 : ℝ)))
    (fun t _ X => impulse_nonneg p X t)
  obtain ⟨G, dG, -, -, hGa, hdGa, hGd⟩ := hr.L1_rep
  have hi (t : ℝ) (_ht : 0 ≤ t) (i : Fin 2) : Integrable (SpatialCalculus.partialD i (ρ t)) :=
    (hD i).integrable t
  have hii (t : ℝ) (_ht : 0 ≤ t) (i : Fin 2) :
      Integrable (SpatialCalculus.partialD i (SpatialCalculus.partialD i (ρ t))) :=
    (hDD i i).integrable t
  refine ⟨?_, fun t => hr.continuous.integrable t, ?_⟩
  · simpa only [hFr] using hp
  · apply scalar_mass hb table terminal ν m hν p (hρ.of_le (by exact WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))) hi hii heq' hGa ?_ hGd hzero
    intro t ht
    have hh := hdGa t ht
    exact hh.trans (Filter.Eventually.of_forall (hd t ht))

theorem detection_of_C1Tails (hν : 0 < ν) (c₀ : Configuration (Fin N)) {ρ : ScalarField 2}
    (hρ : ContDiff ℝ ∞ (uncurry ρ)) (hr : C1Tails ρ)
    (hD : ∀ i, ContinuousTails (spatialD i ρ))
    (hDD : ∀ i k, ContinuousTails (spatialD k (spatialD i ρ)))
    (heq : ∀ t ≥ 0, ∀ X, timeD ρ t X + advection (field hb table terminal ν m) ρ t X =
      ν * laplacian ρ t X + impulse (point hb table terminal ν m c₀ 0) t X)
    (hzero : ∀ X, ρ 0 X = 0) (hm : 1 ≤ m)
    (hc₀ : c₀.leftStack < capacity b m 0 ∧ c₀.rightStack < capacity b m 0)
    (hdir : IncomingDirection table) (hin : IncomingRule table)
    (hterm : NoOutgoing table terminal) (hcont : Continues hb table terminal c₀)
    (hinit : c₀.state ≠ terminal) :
    Observation.planeEvent (liftVelocity (field hb table terminal ν m) ρ) ↔
      Reaches hb table terminal c₀ := by
  obtain ⟨hp, hi, hm'⟩ := scalar_properties_of_C1Tails hb table terminal ν m hν
    (point hb table terminal ν m c₀ 0) hρ hr hD hDD heq hzero
  apply scalar_detection hb table terminal ν m c₀ hν (hρ.of_le (by exact WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))) ?_ hzero
    (fun t _ => hi t) hp hm' hm hc₀ hdir hin hterm hcont hinit
  intro t ht X
  rw [← JointCalculus.timeD_eq_deriv ht X (hρ.differentiable (by simp) (t, X))]
  exact heq t ht X

theorem scalar_lift_unique (hν : 0 < ν) (p : Coord 2) {ρ : ScalarField 2}
    (hρ : ContDiff ℝ ∞ (uncurry ρ)) (hr : C1Tails ρ)
    (hD : ∀ i, ContinuousTails (spatialD i ρ))
    (hDD : ∀ i k, ContinuousTails (spatialD k (spatialD i ρ)))
    (heq : ∀ t ≥ 0, ∀ X, timeD ρ t X + advection (field hb table terminal ν m) ρ t X =
      ν * laplacian ρ t X + impulse p t X)
    (hzero : ∀ X, ρ 0 X = 0)
    {v : VectorField 3} {q : ScalarField 3}
    (hv : Cylinder.ComparisonClass (fun t x => v t (Cylinder.join x))
      (fun t x => q t (Cylinder.join x)))
    (hNS : NavierStokes ν v q (force hb table terminal ν m p)) :
    ∀ t ≥ 0, (∀ x, v t x = liftVelocity (field hb table terminal ν m) ρ t x) ∧
      (∀ x, q t x = 0) := by
  exact Cylinder.comparison_unique_coordinates hν.le
    (comparisonClass_of_scalar_tails hb table terminal ν m hν hρ hr hD hDD) hv
    (force_NavierStokes hb table terminal ν m hν p ρ heq hzero) hNS

end VelocityDetection.ExpandingArray
end

end OAI
