import Mathlib

namespace OAI

namespace InvariantProjection.FiniteConvolution

abbrev Coefficients (K : ℕ) := Fin (2 * K + 1) → ℂ

def center (K : ℕ) : Fin (2 * K + 1) := ⟨K, by omega⟩

noncomputable def polynomial {K : ℕ} (a : Coefficients K) : Polynomial ℂ :=
  ∑ i : Fin (2 * K + 1), Polynomial.monomial (i : ℕ) (a i)

noncomputable def lowProduct {K : ℕ} (a b : Coefficients K) : Coefficients K :=
  fun n => (polynomial a * polynomial b).coeff (n : ℕ)

end InvariantProjection.FiniteConvolution

end OAI
