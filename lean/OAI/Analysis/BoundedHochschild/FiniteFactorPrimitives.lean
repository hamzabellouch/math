import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts
import OAI.Analysis.BoundedHochschild.FactorPrimitive
import OAI.Analysis.BoundedHochschild.TypeIICorners
import OAI.Analysis.BoundedHochschild.CenterPowers
import OAI.Analysis.BoundedHochschild.HomogeneousPrimitives
import OAI.Analysis.BoundedHochschild.MinimalFactors

namespace OAI

/-! Bounded Hochschild primitives for arbitrary finite factors. -/

noncomputable section

open scoped ComplexOrder
namespace BoundedHochschild
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)

theorem primitive_of_finite_factor
    (hτ : TraceInPredual e τ) (h1 : τ 1=1)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (hfactor : ∀ a : M, (∀ x : M, Commute a x) → ∃ c : ℂ, a=c • (1:M))
    {n : ℕ} (f : Cochain M (n+1))
    (hf : ∀ x : Fin (n+2) → M, differentialValue f x=0) :
    ∃ g : Cochain M n, ‖g‖≤12*‖f‖ ∧ ∀ x, differentialValue g x=f x := by
  classical
  by_cases hdiff : HochschildDiffuse.NoMinimalProjections M
  · exact primitive_of_factor e τ hτ h1 htr hfaith hfactor hdiff f hf
  · obtain ⟨d,E,i,hi⟩ := HochschildMinimalFactor.exists_abelian_matrix_system e τ hτ h1 htr hfaith hfactor hdiff
    obtain ⟨g,hg,he⟩ := primitive_of_abelian_matrix_diagonal e E i hi f hf
    exact ⟨g,hg.trans (by nlinarith [norm_nonneg f]),he⟩

end BoundedHochschild

end

end OAI
