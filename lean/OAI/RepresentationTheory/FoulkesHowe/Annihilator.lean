import OAI.RepresentationTheory.FoulkesHowe.MonomialMultilinear
import OAI.RepresentationTheory.FoulkesHowe.FoulkesDiagonal

namespace OAI

noncomputable section

universe u

namespace Problem346

/-- The diagonal vanishing criterion forces every canonical Foulkes map to be
surjective. This dual separation argument does not require finite dimension. -/
theorem IsFoulkesMap.surjective_of_vanishing (a b : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V]
    (μ : SymPow b (SymPow a V) →ₗ[ℂ] SymPow a (SymPow b V))
    (hμ : IsFoulkesMap a b V μ)
    (hvan : ∀ T : SymmetricMultilinearForm a b V,
      IsSymmetricMultilinearForm a b V T →
      (∀ u : Fin b → V, T (fun _ => symMonomial b V u) = 0) → T = 0) :
    Function.Surjective μ := by
  apply LinearMap.dualMap_injective_iff.mp
  rw [← LinearMap.ker_eq_bot]
  apply le_antisymm ?_ bot_le
  intro φ hφ
  change φ = 0
  rw [LinearMap.mem_ker] at hφ
  apply (monomialFunctional_eq_zero_iff a b V φ).mp
  apply hvan _ (monomialFunctional_symmetric a b V φ)
  intro u
  rw [monomialFunctional_apply, ← hμ.map_diagonal a b V μ u]
  have h := congrArg (fun L : SymPow b (SymPow a V) →ₗ[ℂ] ℂ =>
    L (symMonomial b (SymPow a V) (fun j => symMonomial a V (fun _ => u j)))) hφ
  exact h

end Problem346

end

end OAI
