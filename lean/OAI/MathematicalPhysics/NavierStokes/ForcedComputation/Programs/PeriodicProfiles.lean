import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.LogarithmicForce
import OAI.MathematicalPhysics.NavierStokes.ShearFlows.PeriodicCalculus

namespace OAI

/-!
# Periodic profiles supply the logarithmic-force bounds

The phase bounds used in the slow-clock estimate follow from smoothness and
periodicity of the original field. They are not extra decay assumptions.
-/

noncomputable section
open scoped ContDiff
open ShearFlows

namespace ForcedComputation

theorem iteratedDeriv_eq_mixedTime {V : Velocity} (hV : ContDiff ℝ ∞ V)
    (n : ℕ) (t : ℝ) (x : Space) :
    iteratedDeriv n (fun s => V (s, x)) t =
      mixedDerivative V (List.replicate n 0) (t, x) := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv n (fun s => V (s, x)) =
        fun s => mixedDerivative V (List.replicate n 0) (s, x) := funext ih
    rw [he]
    change timeDerivative (mixedDerivative V (List.replicate n 0)) t x = _
    rw [timeDerivative_eq (mixedDerivative_smooth hV _)]
    rfl

theorem periodic_uniformTimeBounds {L : ℝ} (hL : 0 < L) {V : Velocity}
    (hV : ContDiff ℝ ∞ V) (hs : SpatiallyPeriodic L V) (ht : TimePeriodic V) :
    UniformTimeBounds (fun x s => V (s, x)) := by
  intro n
  obtain ⟨C, hC, hb⟩ := periodic_boundedMixedDerivatives hL hV hs ht (List.replicate n 0)
  exact ⟨C, hC, fun x s => by rw [iteratedDeriv_eq_mixedTime hV]; exact hb (s, x)⟩

theorem quadraticPhase_smooth {V : Velocity} (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (fun y : SpaceTime => quadraticPhase V y.2 y.1) :=
  ((timeDerivative_smooth hV).add ((spatial_fderiv_smooth hV).clm_apply hV)).sub hV

theorem quadraticPhase_spatially_periodic {L : ℝ} {V : Velocity}
    (hV : ContDiff ℝ ∞ V) (hs : SpatiallyPeriodic L V) :
    SpatiallyPeriodic L (fun y : SpaceTime => quadraticPhase V y.2 y.1) := by
  intro t x n
  simp only [quadraticPhase, timeDerivative_eq hV]
  change mixedDerivative V [0] (t, x + latticeVector L n) +
      advection (fun y => V (t, y)) (x + latticeVector L n) - V (t, x + latticeVector L n) =
    mixedDerivative V [0] (t, x) + advection (fun y => V (t, y)) x - V (t, x)
  rw [mixedDerivative_spatially_periodic hV hs, hs]
  congr 2
  unfold advection
  have hd := CubePeriodic.fderiv (show CubePeriodic L (fun y => V (t, y)) from hs t)
    ((hV.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp))
  rw [hd x n]
  dsimp only
  rw [hs t x n]

theorem quadraticPhase_time_periodic {V : Velocity}
    (hV : ContDiff ℝ ∞ V) (ht : TimePeriodic V) :
    TimePeriodic (fun y : SpaceTime => quadraticPhase V y.2 y.1) := by
  intro t x
  have he : (fun y => V (t + 1, y)) = fun y => V (t, y) := funext (ht t)
  simp only [quadraticPhase, timeDerivative_eq hV]
  change mixedDerivative V [0] (t + 1, x) + advection (fun y => V (t + 1, y)) x -
      V (t + 1, x) = mixedDerivative V [0] (t, x) + advection (fun y => V (t, y)) x - V (t, x)
  rw [mixedDerivative_time_periodic hV ht, he, ht]

theorem viscousPhase_smooth {V : Velocity} (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (fun y : SpaceTime => viscousPhase V y.2 y.1) := laplacian_smooth hV

theorem viscousPhase_spatially_periodic {L : ℝ} {V : Velocity}
    (hV : ContDiff ℝ ∞ V) (hs : SpatiallyPeriodic L V) :
    SpatiallyPeriodic L (fun y : SpaceTime => viscousPhase V y.2 y.1) := by
  intro t x n
  change laplacian (fun y => V (t, y)) (x + latticeVector L n) =
    laplacian (fun y => V (t, y)) x
  simp only [laplacian_eq_mixed hV]
  apply Finset.sum_congr rfl
  intro j _
  exact mixedDerivative_spatially_periodic hV hs _ t x n

theorem viscousPhase_time_periodic {V : Velocity} (hV : ContDiff ℝ ∞ V)
    (ht : TimePeriodic V) : TimePeriodic (fun y : SpaceTime => viscousPhase V y.2 y.1) := by
  intro t x
  change laplacian (fun y => V (t + 1, y)) x = laplacian (fun y => V (t, y)) x
  simp only [laplacian_eq_mixed hV]
  apply Finset.sum_congr rfl
  intro j _
  exact mixedDerivative_time_periodic hV ht _ t x

theorem quadraticPhase_uniformTimeBounds {L : ℝ} (hL : 0 < L) {V : Velocity}
    (hV : ContDiff ℝ ∞ V) (hs : SpatiallyPeriodic L V) (ht : TimePeriodic V) :
    UniformTimeBounds (quadraticPhase V) := by
  exact periodic_uniformTimeBounds (V := fun y => quadraticPhase V y.2 y.1)
    hL (quadraticPhase_smooth hV)
    (quadraticPhase_spatially_periodic hV hs) (quadraticPhase_time_periodic hV ht)

theorem viscousPhase_uniformTimeBounds {L : ℝ} (hL : 0 < L) {V : Velocity}
    (hV : ContDiff ℝ ∞ V) (hs : SpatiallyPeriodic L V) (ht : TimePeriodic V) :
    UniformTimeBounds (viscousPhase V) := by
  exact periodic_uniformTimeBounds (V := fun y => viscousPhase V y.2 y.1)
    hL (viscousPhase_smooth hV)
    (viscousPhase_spatially_periodic hV hs) (viscousPhase_time_periodic hV ht)

theorem periodic_slowForce_time_decay {L : ℝ} (hL : 0 < L) (ν : ℝ) {V : Velocity}
    (hV : ContDiff ℝ ∞ V) (hs : SpatiallyPeriodic L V) (ht : TimePeriodic V) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x t, 0 ≤ t →
      ‖iteratedDeriv n (fun s => slowForce ν V (s, x)) t‖ ≤ C * (1 + t)⁻¹ ^ (1 + n) := by
  have hQ : ∀ x, ContDiff ℝ ∞ (quadraticPhase V x) := by
    intro x
    exact (quadraticPhase_smooth hV).comp (contDiff_id.prodMk contDiff_const)
  have hD : ∀ x, ContDiff ℝ ∞ (viscousPhase V x) := by
    intro x
    exact (viscousPhase_smooth hV).comp (contDiff_id.prodMk contDiff_const)
  exact slowForce_time_decay (V := V) ν hQ hD (quadraticPhase_uniformTimeBounds hL hV hs ht)
    (viscousPhase_uniformTimeBounds hL hV hs ht) n

end ForcedComputation

end

end OAI
