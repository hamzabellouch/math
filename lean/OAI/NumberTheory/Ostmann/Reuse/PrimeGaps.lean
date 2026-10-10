import OAI.NumberTheory.PrimeGaps.Main

namespace OAI

namespace LargePrimeGaps
open Filter

theorem quantitative_PNT :
    ∀ A : ℝ, 0 < A → ∃ M > 0, ∀ᶠ X : ℕ in atTop,
      |(∑ n ∈ Finset.Ioc 0 X, ArithmeticFunction.vonMangoldt n) - (X : ℝ)| ≤
        M * (X : ℝ) * (Real.log X) ^ (-A) :=
  BombieriVinogradov_quantitative_PNT bombieriVinogradov

end LargePrimeGaps

end OAI
