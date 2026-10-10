import OAI.Algebra.Finitistic.Selected.SelectedBaseIterates
import OAI.Algebra.Finitistic.Selected.SelectedOrdinaryDimension

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.SelectedFiniteAmplitude
open SelectedOrdinaryAlgebra SelectedBaseIterates
local instance : HasDerivedCategory.{1} (ModuleCat.{0} D) :=
  HasDerivedCategory.standard (ModuleCat.{0} D)

/-- Every genuine X-derived iterate of each actual test input has finite amplitude.
The extra two degrees per iteration are harmless for the finite-dimension argument. -/
theorem bounded (Y : FiniteSelectionFamily.S.{0}) (r : ℕ) :
    (object Y r).IsGE (-((r * (3 * length + 4) : ℕ) : ℤ)) ∧
    (object Y r).IsLE 0 := by
  simpa only [SelectedOrdinaryDimension.bound, Nat.add_assoc] using
    SelectedBaseIterates.bounded SelectedOrdinaryDimension.bound
      SelectedOrdinaryDimension.left_module Y r

/-- A nonzero actual iterate is detected in a finite, explicit cohomological window. -/
theorem nonzero_in_window (Y : FiniteSelectionFamily.S.{0}) (r : ℕ)
    (h : ¬ Limits.IsZero (object Y r)) :
    ∃ n : ℕ, n ≤ r * (3 * length + 4) ∧
      ¬ Limits.IsZero ((DerivedCategory.homologyFunctor (ModuleCat D) (-(n : ℤ))).obj
        (object Y r)) := by
  simpa only [SelectedOrdinaryDimension.bound, Nat.add_assoc] using
    DerivedBar.IterateSupport.nonzero_in_finite_window ℂ D
      SelectedOrdinaryDimension.bound SelectedOrdinaryDimension.left_module X (input Y) r h

/-- Any additive terminal tensor applied to a resolved actual iterate has a
uniform finite homological bound. This supplies the later residue/simple tests. -/
theorem terminal_exact {E : Type*} [Category E] [Abelian E]
    (F : ModuleCat.{0} D ⥤ E) [F.Additive]
    (Y : FiniteSelectionFamily.S.{0}) (r n : ℕ)
    (hn : (r+1) * (3 * length + 4) < n) :
    ((F.mapHomologicalComplex (.down ℕ)).obj
      (DerivedBar.barTotal ℂ D (DerivedBar.IterateSupport.resolvedModel ℂ D X (input Y) r))).ExactAt n := by
  apply DerivedBar.IterateSupport.iterated_additive_exact_above ℂ D F
    SelectedOrdinaryDimension.bound SelectedOrdinaryDimension.left_module X (input Y) r n
  simpa only [SelectedOrdinaryDimension.bound, Nat.add_assoc] using hn
end LittleFinitistic.SelectedFiniteAmplitude

end

end OAI
