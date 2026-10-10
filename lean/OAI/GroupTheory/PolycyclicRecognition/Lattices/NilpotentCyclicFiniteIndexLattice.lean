import OAI.GroupTheory.PolycyclicRecognition.Lattices.NilpotentLatticeDerivationLog
import OAI.GroupTheory.PolycyclicRecognition.Geometry.RealLieAutomorphismPowerLog

namespace OAI

/-! # Cyclic extensions of the constructed nilpotent lattice model -/

noncomputable section
namespace PolycyclicRecognition.NilpotentLatticeCoordinates
variable {H : Type} [Group H] (C : NilpotentLatticeCoordinates H)
include C

theorem cyclic_finiteIndex_lattice (a : MulAut H) :
    ∃ Γ : Subgroup (H ⋊[integerPowerAction a] Multiplicative ℤ), Γ.FiniteIndex ∧
      ∃ (S : SimplyConnectedSolvableLieModel) (Λ : Subgroup S.carrier),
        IsUniformLattice Λ ∧ Nonempty (Γ ≃* Λ) := by
  obtain ⟨m, hm, D, hD⟩ := real_lie_automorphism_has_power_log (C.automorphismLieEquiv a)
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
