import OAI.Algebra.Finitistic.Selected.SelectedOrdinaryOrbit
import OAI.Algebra.Finitistic.Selected.SelectedPDConclusion
import OAI.Algebra.Finitistic.Basic

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.Main
open SelectedOrdinaryAlgebra SelectedOrdinaryModules

/-- The fixed algebra and every actual witness are finite dimensional over ℂ. -/
theorem algebra_finite : FiniteDimensional ℂ A := inferInstance

theorem test_finite (m : ℕ) [NeZero m] : FiniteDimensional ℂ (testModule m) := inferInstance

/-- For the one fixed finite-dimensional complex algebra constructed in the
manuscript, every positive m has the actual finite module N_m with the stated
finite projective-dimension bounds. -/
theorem projective_dimension_bounds (m : ℕ) [NeZero m] :
    ((2*m-2 : ℕ) : WithBot ℕ∞) ≤ projectiveDimension (testModule m) ∧
      projectiveDimension (testModule m) < ⊤ := by
  have h := SelectedOrdinaryOrbit.extinction m
  exact ⟨SelectedPDConclusion.lower_bound_of_survival (FiniteSelectionFamily.test m) (2*m-2) h.2,
    SelectedPDConclusion.finite_pd_of_extinction (FiniteSelectionFamily.test m) (2*m) h.1⟩

/-- The actual constructed algebra has infinite little finitistic dimension. -/
theorem infinite_littleFinitisticDimension : littleFinitisticDimension A = ⊤ := by
  apply littleFinitisticDimension_eq_top_of_two_mul_bounds
  intro m hm
  let : NeZero m := ⟨by omega⟩
  exact ⟨testModule m, inferInstance, (projective_dimension_bounds m).2,
    (projective_dimension_bounds m).1⟩

/-- Main theorem, with finite dimensionality of the one fixed A explicit and
with actual finitely generated witness modules for every positive m. -/
theorem counterexample : FiniteDimensional ℂ A ∧ littleFinitisticDimension A = ⊤ ∧
    ∀ m : ℕ, 0 < m → ∃ N : ModuleCat.{0} A, Module.Finite A N ∧
      ((2*m-2 : ℕ) : WithBot ℕ∞) ≤ projectiveDimension N ∧ projectiveDimension N < ⊤ := by
  refine ⟨inferInstance, infinite_littleFinitisticDimension, ?_⟩
  intro m hm
  let : NeZero m := ⟨by omega⟩
  exact ⟨testModule m, inferInstance, projective_dimension_bounds m⟩

theorem exists_counterexample :
    ∃ (A : Type) (_ : Ring A) (_ : Algebra ℂ A),
      FiniteDimensional ℂ A ∧ littleFinitisticDimension A = ⊤ ∧
        ∀ m : ℕ, 0 < m → ∃ N : ModuleCat.{0} A, Module.Finite A N ∧
          ((2*m-2 : ℕ) : WithBot ℕ∞) ≤ projectiveDimension N ∧
            projectiveDimension N < ⊤ := by
  exact ⟨SelectedOrdinaryAlgebra.A, inferInstance, inferInstance, counterexample⟩

end LittleFinitistic.Main

end

end OAI
