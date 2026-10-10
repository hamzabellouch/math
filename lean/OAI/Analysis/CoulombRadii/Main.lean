import Mathlib
import OAI.Analysis.CoulombRadii.Screening.AtomicMasterFresh
import OAI.Analysis.CoulombRadii.RandomFields.ObservationFieldTransfer
import OAI.Analysis.CoulombRadii.RandomFields.PhysicalBandRegularity
import OAI.Analysis.CoulombRadii.LimitTheory.AdmissibleStage

namespace OAI

section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff
noncomputable section
namespace NeutralAtom

theorem generalized_outer_radii
    (Ψ : ∀ N : ℕ, Wavefunction (N + 1))
    (hΨ : ∀ N : ℕ, IsNormalizedGroundState (N + 1) (Ψ N)) :
    Tendsto (fun m : ℕ => (((m : ℝ) ^ (1 / 3 : ℝ) : ℝ) : EReal) * upperRadius Ψ m)
      atTop (𝓝 (bTF : EReal)) ∧
    Tendsto (fun m : ℕ => (((m : ℝ) ^ (1 / 3 : ℝ) : ℝ) : EReal) * lowerRadius Ψ m)
      atTop (𝓝 (bTF : EReal)) := by
  obtain ⟨Zbar,htail⟩ := physical_expected_exterior_asymptotic
  exact iterated_limits_of_expected_exterior_asymptotic Zbar htail Ψ hΨ
end NeutralAtom
end

end

end OAI
