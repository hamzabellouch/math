import OAI.MathematicalPhysics.RapidForcing.NSUniqueness
import OAI.MathematicalPhysics.RapidForcing.SchwartzRestriction

namespace OAI


namespace RapidForcing

theorem addressed_analytic_realization (ν : ℝ) (hν : 0 < ν) (M : Machine) (w : M.Input) :
    let u := addressedVelocity M w
    let f := addressedForce ν M w
    Smooth f ∧ Supported f ∧ Rapid f ∧ RapidSpaceTime f ∧
    Smooth u ∧ Supported u ∧ Rapid u ∧ RapidSpaceTime u ∧
    UniqueEnergySolution ν f u (fun _ _ => 0) ∧
    ∃ X : ℝ → Space → Space, MaterialFlow u X ∧
      (M.Halts w ↔ ∃ t : ℝ, 0 ≤ t ∧ (X t 0) 0 < -1) := by
  obtain ⟨hfS, hfK, huS, huK, _⟩ := addressed_classical_solution ν M w
  obtain ⟨huR, huRX, hfR, hfRX⟩ := addressed_fields_rapid ν M w
  exact ⟨hfS, hfK, hfR, hfRX, huS, huK, huR, huRX,
    addressed_uniqueEnergySolution hν.le M w, addressed_particle_detection M w⟩

end RapidForcing

end OAI
