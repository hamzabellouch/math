import OAI.GroupTheory.PolycyclicRecognition.Geometry.TriangularHeight
import Mathlib.Algebra.Lie.Solvable

namespace OAI

/-! # Solvability from a real triangular adjoint basis -/

noncomputable section
namespace PolycyclicRecognition

open LieAlgebra

theorem TriangularAdjoint.lieAlgebra_isSolvable
    {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
    {n : ℕ} (T : TriangularAdjoint L n) : LieAlgebra.IsSolvable L := by
  let : LieRing.IsNilpotent T.kernelIdeal := T.kernelIdeal_nilpotent
  have hder : derivedSeries ℝ L 1 ≤ T.kernelIdeal := by
    intro z hz
    change z ∈ (derivedSeries ℝ L 1 : Submodule ℝ L) at hz
    rw [coe_derivedSeries_one_eq] at hz
    exact (Submodule.span_le.mpr (by
      rintro _ ⟨x, y, rfl⟩
      exact (T.mem_kernelIdeal _).mpr fun i => T.character_lie i x y) hz :
        z ∈ T.kernelIdeal.toSubmodule)
  obtain ⟨k, hk⟩ := IsSolvable.solvable ℝ T.kernelIdeal
  have hK : derivedSeriesOfIdeal ℝ L k T.kernelIdeal = ⊥ :=
    (LieIdeal.derivedSeries_eq_bot_iff T.kernelIdeal k).mp hk
  apply IsSolvable.mk (R := ℝ) (k := k + 1)
  apply le_antisymm _ bot_le
  change derivedSeriesOfIdeal ℝ L (k + 1) ⊤ ≤ ⊥
  rw [derivedSeriesOfIdeal_add]
  exact (derivedSeriesOfIdeal_mono hder k).trans (le_of_eq hK)

end PolycyclicRecognition

end

end OAI
