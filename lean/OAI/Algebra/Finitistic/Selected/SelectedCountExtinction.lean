import OAI.Algebra.Finitistic.Selected.SelectedCountCohomology
import OAI.Algebra.Finitistic.Iteration.IntegerIterateExtinction

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.SelectedCountExtinction
open SelectedOrdinaryAlgebra SelectedBaseIterates SelectedCountCohomology
local instance : HasDerivedCategory.{1} (ModuleCat.{0} D) :=
  HasDerivedCategory.standard (ModuleCat.{0} D)

/-- After actual tensor extinction, all later original count summands vanish. -/
theorem tail_zero (Y : FiniteSelectionFamily.S.{0}) (t r : ℕ) (htr : t ≤ r)
    (h : IsZero (object Y t)) : IsZero (count Y r) :=
  (SelectedCountCohomology.isZero_iff Y r).mpr
    (DerivedBar.IterateSupport.zero_of_le ℂ D X (input Y) t r htr h)

/-- A zero iterate gives one finite cohomological window for the entire original
count family, including the infinitely many counts that have already vanished. -/
theorem uniform_bounded (Y : FiniteSelectionFamily.S.{0}) (t : ℕ)
    (h : IsZero (object Y t)) (r : ℕ) :
    (count Y r).IsGE (-((t * (3 * length + 5) : ℕ) : ℤ)) ∧ (count Y r).IsLE 0 := by
  have := (SelectedCountCohomology.bounded Y r).1
  have := (SelectedCountCohomology.bounded Y r).2
  constructor
  · by_cases htr : t ≤ r
    · apply (DerivedCategory.isGE_iff _ _).mpr
      intro i _
      exact (DerivedCategory.homologyFunctor (ModuleCat D) i).map_isZero (tail_zero Y t r htr h)
    · apply DerivedCategory.TStructure.t.isGE_of_ge (count Y r)
        (-((t * (3 * length + 5) : ℕ) : ℤ)) (-((r * (3 * length + 5) : ℕ) : ℤ)) ?_
      have hm := Nat.mul_le_mul_right (3 * length + 5) (show r ≤ t by omega)
      exact neg_le_neg (by exact_mod_cast hm)
  · exact DerivedCategory.TStructure.t.isLE_of_le (count Y r) (-(r : ℤ)) 0 (by omega)

/-- Every original count has zero cohomology outside that single finite window. -/
theorem uniform_homology_zero (Y : FiniteSelectionFamily.S.{0}) (t : ℕ)
    (h : IsZero (object Y t)) (r : ℕ) (i : ℤ)
    (hi : i < -((t * (3 * length + 5) : ℕ) : ℤ) ∨ 0 < i) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat D) i).obj (count Y r)) := by
  have := (uniform_bounded Y t h r).1
  have := (uniform_bounded Y t h r).2
  exact hi.elim (fun h => DerivedCategory.isZero_of_isGE _ _ i h)
    (fun h => DerivedCategory.isZero_of_isLE _ 0 i h)
end LittleFinitistic.SelectedCountExtinction

end

end OAI
