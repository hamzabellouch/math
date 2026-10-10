import OAI.LinearAlgebra.CirculantHadamard.Witnesses
import OAI.LinearAlgebra.CirculantHadamard.OrderReduction
import OAI.LinearAlgebra.CirculantHadamard.BinaryContradiction
import Lean.Elab.Tactic.Omega

namespace OAI

/-!
# Classification of positive real circulant sign Hadamard orders

The existence predicate retains the actual real matrix, its sign entries,
literal cyclic rows, and full Gram identity. Square-order and two-adic descent
reduce every nontrivial order to `4 * u^2` with `u` positive and odd. The binary
contradiction excludes `u > 1`, while explicit matrices realize orders one and four.
-/

namespace CirculantHadamard

/-- An actual real circulant sign Hadamard matrix of positive order exists
exactly at orders one and four. -/
theorem exists_iff_order_one_or_four (n : ℕ) (hn : 0 < n) :
    ExistsRealCirculantHadamard n ↔ n = 1 ∨ n = 4 := by
  constructor
  · intro hH
    by_cases hn1 : n = 1
    · exact Or.inl hn1
    · have hnlarge : 1 < n := by omega
      rcases order_reduction hnlarge hH with ⟨u, hu, hodd, rfl⟩
      by_cases hu1 : u = 1
      · right
        simp [hu1]
      · have hul : 1 < u := by omega
        exact (not_exists_four_mul_odd_square hul hodd hH).elim
  · exact exists_of_order_one_or_four

end CirculantHadamard

end OAI
