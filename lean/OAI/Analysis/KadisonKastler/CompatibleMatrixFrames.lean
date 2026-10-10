import OAI.Analysis.KadisonKastler.FullMatrixRefinement
import OAI.Analysis.KadisonKastler.Algebra

namespace OAI

/-! # Compatible finite groups for an increasing matrix chain

The finite index set is retained as data, so tensor refinements do not
require changing the represented operators or reindexing to a fixed type.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A full matrix system for a concrete algebra, with a finite nonempty index. -/
structure FullMatrixFrame (A : StarSubalgebra ℂ (H →L[ℂ] H)) where
  Index : Type
  fintype : Fintype Index
  decidableEq : DecidableEq Index
  point : Index
  units : Generator.MatrixUnitSystem Index A
  full : Function.Surjective units.hom

attribute [instance] FullMatrixFrame.fintype FullMatrixFrame.decidableEq

namespace FullMatrixFrame

variable {A B : StarSubalgebra ℂ (H →L[ℂ] H)}

instance index_nonempty (F : FullMatrixFrame A) : Nonempty F.Index := ⟨F.point⟩

def ambientUnits (F : FullMatrixFrame A) : Generator.MatrixUnitSystem F.Index (H →L[ℂ] H) :=
  F.units.map A.subtype

def group (F : FullMatrixFrame A) : Subgroup (unitary (H →L[ℂ] H)) :=
  matrixSignedGroup F.ambientUnits

instance group_finite (F : FullMatrixFrame A) : Finite F.group :=
  matrixSignedGroup_finite _

theorem ambientUnits_algebra (F : FullMatrixFrame A) : F.ambientUnits.algebra = A := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    change (F.units.map A.subtype).hom a ∈ A
    rw [matrixUnits_map_hom]
    exact (F.units.hom a).property
  · intro hx
    obtain ⟨a, ha⟩ := F.full ⟨x, hx⟩
    refine ⟨a, ?_⟩
    change (F.units.map A.subtype).hom a = x
    rw [matrixUnits_map_hom, ha]
    rfl

theorem group_mem (F : FullMatrixFrame A) (u : F.group) : (u : H →L[ℂ] H) ∈ A := by
  obtain ⟨g, hg⟩ := u.property
  have h := F.ambientUnits_algebra.le (matrixUnitSignedRepresentation_mem F.ambientUnits g)
  rw [hg] at h
  exact h

/-- The represented finite group determines the full matrix commutant. -/
theorem commutes_of_group (F : FullMatrixFrame A) (T : H →L[ℂ] H)
    (hT : ∀ u : F.group, Commute (u : H →L[ℂ] H) T) :
    ∀ a ∈ A, Commute a T := by
  have hc : ∀ a ∈ F.ambientUnits.algebra, Commute a T := by
    apply (F.ambientUnits.commute_algebra_iff T).mpr
    apply commute_matrixUnits_of_signed
    intro g
    exact hT ⟨matrixUnitSignedRepresentation F.ambientUnits g, ⟨g, rfl⟩⟩
  intro a ha
  exact hc a (F.ambientUnits_algebra.symm.le ha)

/-- A full matrix frame is obtained from a specified matrix-unit range. -/
def ofUnits {ι : Type} [Fintype ι] [DecidableEq ι]
    (E : Generator.MatrixUnitSystem ι (H →L[ℂ] H)) (o : ι) : FullMatrixFrame E.algebra := by
  let P : Generator.MatrixUnitSystem ι E.algebra :=
    { entry i j := ⟨E.entry i j, E.entry_mem i j⟩
      star_entry i j := Subtype.ext (E.star_entry i j)
      mul_entry i j k l := Subtype.ext (by
        change E.entry i j * E.entry k l = _
        rw [E.mul_entry]
        split_ifs <;> rfl)
      total := Subtype.ext (by simpa using E.total) }
  refine ⟨ι, inferInstance, inferInstance, o, P, ?_⟩
  rintro ⟨x, a, ha⟩
  refine ⟨a, Subtype.ext ?_⟩
  change ((P.hom a : E.algebra) : H →L[ℂ] H) = x
  calc
    _ = E.hom a := by
      change E.algebra.subtype (P.hom a) = _
      rw [← matrixUnits_map_hom]
      rfl
    _ = x := ha

variable [Nontrivial H]

/-- Refine a frame inside a larger full matrix algebra while retaining the
actual ambient finite group. -/
theorem exists_refinement (E : FullMatrixFrame A) (P : FullMatrixFrame B) (hAB : A ≤ B) :
    ∃ F : FullMatrixFrame B, E.group ≤ F.group := by
  let j := StarSubalgebra.inclusion hAB
  obtain ⟨r, Q, hr, hfull, hretain, _⟩ := exists_matrix_refinement_in_full_matrix_algebra
    P.units P.full (E.units.map j) E.point
  let F : FullMatrixFrame B :=
    ⟨E.Index × Fin r, inferInstance, inferInstance, (E.point, ⟨0, hr⟩), Q, hfull⟩
  refine ⟨F, ?_⟩
  apply matrixSignedGroup_refinement E.ambientUnits F.ambientUnits
  intro i k
  change (∑ a, ((Q.entry (i, a) (k, a) : B) : H →L[ℂ] H)) =
    ((E.units.entry i k : A) : H →L[ℂ] H)
  have hh := congrArg (fun b : B => (b : H →L[ℂ] H)) (hretain i k)
  simpa [Generator.MatrixUnitSystem.map_entry, j] using hh

end FullMatrixFrame

variable [Nontrivial H] {A : ℕ → StarSubalgebra ℂ (H →L[ℂ] H)}

/-- Choose compatible frames without changing any algebra in the chain. -/
def compatibleMatrixFrames (F : ∀ n, FullMatrixFrame (A n)) (hA : Monotone A) :
    ∀ n, FullMatrixFrame (A n)
  | 0 => F 0
  | n + 1 => Classical.choose
      (FullMatrixFrame.exists_refinement (compatibleMatrixFrames F hA n) (F (n + 1))
        (hA (Nat.le_succ n)))

theorem compatibleMatrixFrames_group_monotone
    (F : ∀ n, FullMatrixFrame (A n)) (hA : Monotone A) :
    Monotone (fun n => (compatibleMatrixFrames F hA n).group) := by
  apply monotone_nat_of_le_succ
  intro n
  exact Classical.choose_spec
    (FullMatrixFrame.exists_refinement (compatibleMatrixFrames F hA n) (F (n + 1))
      (hA (Nat.le_succ n)))

end

end KadisonKastler

end OAI
