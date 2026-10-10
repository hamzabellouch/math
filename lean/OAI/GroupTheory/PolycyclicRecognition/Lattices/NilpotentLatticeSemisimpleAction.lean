import OAI.GroupTheory.PolycyclicRecognition.Lattices.NilpotentLatticeDerivationLog
import OAI.GroupTheory.PolycyclicRecognition.Geometry.RealSemisimpleLieLogarithm

namespace OAI

/-! # Cyclic lattice extensions with semisimple action -/

noncomputable section
namespace PolycyclicRecognition.NilpotentLatticeCoordinates
variable {H : Type} [Group H] (C : NilpotentLatticeCoordinates H)

theorem cyclic_finiteIndex_lattice_of_semisimple (a : MulAut H)
    (ha : Module.End.IsSemisimple (C.automorphismLinear a)) :
    ∃ Γ : Subgroup (H ⋊[integerPowerAction a] Multiplicative ℤ), Γ.FiniteIndex ∧
      ∃ (S : SimplyConnectedSolvableLieModel) (Λ : Subgroup S.carrier),
        IsUniformLattice Λ ∧ Nonempty (Γ ≃* Λ) := by
  obtain ⟨m, hm, D, hD⟩ := real_semisimple_lie_automorphism_has_power_log
    (C.automorphismLieEquiv a) ha
  apply C.cyclic_finiteIndex_lattice_of_derivation_log a hm D
  apply ContinuousLinearMap.ext
  intro x
  have h := congrArg (fun T : Module.End ℝ C.carrier => T x) hD
  change _ = (C.automorphismLinear (a ^ m)) x
  rw [map_pow]
  exact h

end PolycyclicRecognition.NilpotentLatticeCoordinates

end

end OAI
