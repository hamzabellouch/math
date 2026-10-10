import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Prime.Basic

namespace OAI

namespace Ostmann.Dirichlet

noncomputable def ordinaryPrimeSeriesTerm (sigma : ℝ) (n : ℕ) : ℝ :=
  if n.Prime then Real.log n / (n : ℝ) ^ sigma else 0

lemma ordinaryPrimeSeriesTerm_nonneg (sigma : ℝ) (n : ℕ) :
    0 ≤ ordinaryPrimeSeriesTerm sigma n := by
  unfold ordinaryPrimeSeriesTerm
  split_ifs <;> positivity

end Ostmann.Dirichlet

end OAI
