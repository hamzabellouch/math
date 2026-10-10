import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.PeriodicProfiles

namespace OAI

/-! Spatial derivatives of the slow clock retain its full time decay. -/

noncomputable section
open scoped ContDiff
open ShearFlows

namespace ForcedComputation

def spatialWord : List (Fin 3) → (Space → Space) → Space → Space
  | [], U => U
  | j :: α, U => derivative (spatialWord α U) j

theorem spatialWord_smul (α : List (Fin 3)) (a : ℝ) (U : Space → Space) :
    spatialWord α (fun x => a • U x) = fun x => a • spatialWord α U x := by
  induction α with
  | nil => rfl
  | cons j α ih =>
    simp only [spatialWord, ih]
    funext x
    exact derivative_smul a _ j x

def spatialPhase (V : Velocity) (α : List (Fin 3)) : Velocity :=
  fun y => spatialWord α (fun x => V (y.1, x)) y.2

theorem spatialPhase_eq_mixed {V : Velocity} (hV : ContDiff ℝ ∞ V) (α : List (Fin 3)) :
    spatialPhase V α = mixedDerivative V (α.map Fin.succ) := by
  induction α with
  | nil => rfl
  | cons j α ih =>
    funext y
    change derivative (fun x => spatialPhase V α (y.1, x)) j y.2 = _
    rw [ih, spatialDerivative_eq_mixed (mixedDerivative_smooth hV _)]
    rfl

theorem spatialPhase_smooth {V : Velocity} (hV : ContDiff ℝ ∞ V) (α : List (Fin 3)) :
    ContDiff ℝ ∞ (spatialPhase V α) := by
  rw [spatialPhase_eq_mixed hV]
  exact mixedDerivative_smooth hV _

theorem spatialPhase_uniformTimeBounds {L : ℝ} (hL : 0 < L) {V : Velocity}
    (hV : ContDiff ℝ ∞ V) (hs : SpatiallyPeriodic L V) (ht : TimePeriodic V)
    (α : List (Fin 3)) : UniformTimeBounds (fun x s => spatialPhase V α (s, x)) := by
  rw [spatialPhase_eq_mixed hV]
  exact periodic_uniformTimeBounds hL (mixedDerivative_smooth hV _)
    (mixedDerivative_spatially_periodic hV hs _) (mixedDerivative_time_periodic hV ht _)

theorem spatialWord_logarithmicProfile (r : ℕ) (V : Velocity) (α : List (Fin 3))
    (t : ℝ) (x : Space) :
    spatialWord α (fun y => logarithmicProfile r (fun s => V (s, y)) t) x =
      logarithmicProfile r (fun s => spatialPhase V α (s, x)) t := by
  exact congrFun (spatialWord_smul α ((1 + t)⁻¹ ^ r)
    (fun y => V (Real.log (1 + t), y))) x

theorem periodic_profile_mixed_decay {L : ℝ} (hL : 0 < L) {V : Velocity}
    (hV : ContDiff ℝ ∞ V) (hs : SpatiallyPeriodic L V) (ht : TimePeriodic V)
    (r n : ℕ) (α : List (Fin 3)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x t, 0 ≤ t →
      ‖iteratedDeriv n
        (fun s => spatialWord α (fun y => logarithmicProfile r (fun q => V (q, y)) s) x) t‖ ≤
        C * (1 + t)⁻¹ ^ (r + n) := by
  have hphase (x : Space) : ContDiff ℝ ∞ (fun s => spatialPhase V α (s, x)) :=
    (spatialPhase_smooth hV α).comp (contDiff_id.prodMk contDiff_const)
  obtain ⟨C, hC, hb⟩ := logarithmicProfile_uniform_decay r n hphase
    (spatialPhase_uniformTimeBounds hL hV hs ht α)
  refine ⟨C, hC, fun x t ht => ?_⟩
  have he : (fun s => spatialWord α (fun y => logarithmicProfile r (fun q => V (q, y)) s) x) =
      logarithmicProfile r (fun s => spatialPhase V α (s, x)) :=
    funext (fun s => spatialWord_logarithmicProfile r V α s x)
  rw [he]
  exact hb x t ht

end ForcedComputation

end

end OAI
