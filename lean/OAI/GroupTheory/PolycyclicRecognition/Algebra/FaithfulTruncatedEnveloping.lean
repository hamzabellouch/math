import OAI.GroupTheory.PolycyclicRecognition.Geometry.TruncatedSemidirectRepresentation
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentFaithfulRepresentation

namespace OAI

/-! # A faithful nilpotent representation compatible with derivations

A faithful nilpotent representation determines a truncation degree.
The resulting finite representation carries the full derivation action,
as required for a solvable extension.
-/

noncomputable section
namespace PolycyclicRecognition

open Module

theorem exists_faithful_truncated_enveloping (L : Type) [RealNormedLieAlgebra L]
    [FiniteDimensional ℝ L] (hnil : LieRing.IsNilpotent L) :
    ∃ c : ℕ, FiniteDimensional ℝ (TruncatedEnvelopingAlgebra ℝ L c) ∧
      Function.Injective (truncatedEnvelopingGenerator (R := ℝ) (L := L) c) := by
  obtain ⟨m, c, j, hj, _, hc⟩ := exists_faithful_nilpotent_representation L hnil
  exact ⟨c, finiteDimensional_truncatedEnvelopingAlgebra (finBasis ℝ L) c,
    truncatedEnvelopingGenerator_injective c j hj hc⟩

theorem exists_faithful_truncated_semidirect (L H : Type) [RealNormedLieAlgebra L]
    [FiniteDimensional ℝ L] [LieRing H] [LieAlgebra ℝ H]
    (hnil : LieRing.IsNilpotent L) (ψ : H →ₗ⁅ℝ⁆ LieDerivation ℝ L L)
    (hψ : Function.Injective ψ) :
    ∃ c : ℕ, FiniteDimensional ℝ (TruncatedEnvelopingAlgebra ℝ L c) ∧
      Function.Injective (truncatedSemidirectRepresentation c ψ) := by
  obtain ⟨c, hfin, hgen⟩ := exists_faithful_truncated_enveloping L hnil
  exact ⟨c, hfin, truncatedSemidirectRepresentation_injective c ψ hψ hgen⟩

end PolycyclicRecognition

end

end OAI
