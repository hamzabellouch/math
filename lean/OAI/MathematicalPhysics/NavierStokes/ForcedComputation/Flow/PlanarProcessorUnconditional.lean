import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarVariationDischarge
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarProcessorMain

namespace OAI

/-! The complete planar processor theorem with the smooth-dependence
input discharged for the actual compiled finite Hamiltonian. -/

noncomputable section
namespace ForcedComputation.Recorder.Planar
open ShearFlows

theorem smooth_planar_processor_unconditional (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) (Ω : ℝ → ℝ → Plane → Plane)
    (hΩ : IsPlanarTransition (planarSlice (normalizedHamiltonian I hI)) Ω) :
    ∃ Ψ, ProcessorProperties I hI Ω Ψ :=
  smooth_planar_processor I hI Ω hΩ
    (planarTransition_variations (normalizedHamiltonian_valid I hI)
      (normalizedHamiltonian_noTime I hI) hΩ)

theorem exists_smooth_planar_processor (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) :
    ∃ Ω Ψ, ProcessorProperties I hI Ω Ψ := by
  obtain ⟨Ω, hΩ⟩ := exists_planarTransition (normalizedHamiltonian_valid I hI)
    (normalizedHamiltonian_noTime I hI)
  obtain ⟨Ψ, hΨ⟩ := smooth_planar_processor_unconditional I hI Ω hΩ
  exact ⟨Ω, Ψ, hΨ⟩

end ForcedComputation.Recorder.Planar

end

end OAI
