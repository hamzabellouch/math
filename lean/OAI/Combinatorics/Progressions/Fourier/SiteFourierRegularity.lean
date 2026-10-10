import OAI.Combinatorics.Progressions.Fourier.SiteFourierHaarMean

namespace OAI

section

namespace Erdos3

theorem subspaceArrayCharacter_continuous {I J : Type*} [Fintype I] [Fintype J]
    (U : Submodule ℝ (J → ℝ)) (b : Matrix I J ℤ) :
    Continuous (subspaceArrayCharacter U b) :=
  quotientLinearCharacter_continuous _ _ _
    (subspaceArrayFunctional U (fun i a => (b i a : ℝ))).continuous_of_finiteDimensional

namespace VectorPolynomial

open scoped BigOperators

theorem siteTorusFourierSum_continuous {S F : Type*} [Fintype S] [Fintype F]
    {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (b : F → ∀ j, Matrix S (J j) ℤ) (c : F → ℂ) :
    Continuous (siteTorusFourierSum U b c) := by
  unfold siteTorusFourierSum
  apply continuous_finsetSum
  intro a _
  apply continuous_const.mul
  apply continuous_finsetProd
  intro j _
  exact (subspaceArrayCharacter_continuous (U j) (b a j)).comp (continuous_apply j)

theorem siteTorusFourierSum_norm_le {S F : Type*} [Fintype S] [Fintype F]
    {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (b : F → ∀ j, Matrix S (J j) ℤ) (c : F → ℂ)
    (x : SiteTorus S U) : ‖siteTorusFourierSum U b c x‖ ≤ ∑ a, ‖c a‖ := by
  unfold siteTorusFourierSum
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro a _
  simp [norm_prod, subspaceArrayCharacter_norm]

end VectorPolynomial
end Erdos3

end

end OAI
