import OAI.GroupTheory.PolycyclicRecognition.Geometry.AlgebraTangentLie
import Mathlib.GroupTheory.Solvable

namespace OAI

/-! # Solvability of the infinitesimal action of a solvable matrix group

The group derived series controls successive commutators of the tangent
spans. This avoids assuming a closed-subgroup or Lie–Kolchin theorem.
-/

noncomputable section
namespace PolycyclicRecognition

attribute [local instance 100] LieRing.ofAssociativeRing

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
  [FiniteDimensional ℝ A] [CompleteSpace A]

/-- The tangent Lie algebra of a solvable subgroup of units is solvable. -/
theorem algebraGroupTangentLie_isSolvable (D : Subgroup Aˣ) [Group.IsSolvable D] :
    LieAlgebra.IsSolvable (algebraGroupTangentLie D) := by
  let L := algebraGroupTangentLie D
  let E (n : ℕ) := (derivedSeries D n).map D.subtype
  have hE0 : E 0 = D := by simp [E, ← MonoidHom.range_eq_map]
  have hEs (n : ℕ) : E (n + 1) = ⁅E n, E n⁆ := by
    dsimp [E]
    rw [Subgroup.map_commutator]
  have hbound (n : ℕ) : ∀ x ∈ LieAlgebra.derivedSeries ℝ L n,
      (x : A) ∈ algebraGroupTangentSpan (E n) := by
    induction n with
    | zero =>
      intro x _
      rw [hE0]
      exact x.property
    | succ n ih =>
      intro x hx
      have hh : (LieAlgebra.derivedSeries ℝ L (n + 1)).toSubmodule ≤
          (algebraGroupTangentSpan (E (n + 1))).comap L.incl.toLinearMap := by
        rw [LieAlgebra.derivedSeries_def, LieAlgebra.derivedSeriesOfIdeal_succ,
          LieSubmodule.lieIdeal_oper_eq_linear_span']
        apply Submodule.span_le.mpr
        rintro _ ⟨y, hy, z, hz, rfl⟩
        change (y : A) * (z : A) - (z : A) * (y : A) ∈ algebraGroupTangentSpan (E (n + 1))
        rw [hEs]
        exact algebraGroupTangentSpan_commutator (ih y hy) (ih z hz)
      exact hh hx
  obtain ⟨n, hn⟩ := Group.IsSolvable.solvable (G := D)
  apply (LieAlgebra.isSolvable_iff ℝ L).mpr
  refine ⟨n, le_antisymm ?_ bot_le⟩
  intro x hx
  change x = 0
  apply Subtype.ext
  have hb := hbound n x hx
  simpa only [E, hn, Subgroup.map_bot, algebraGroupTangentSpan_bot,
    Submodule.mem_bot, ZeroMemClass.coe_zero] using hb

end PolycyclicRecognition

end

end OAI
