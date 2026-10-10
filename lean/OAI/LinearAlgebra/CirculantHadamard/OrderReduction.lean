import OAI.LinearAlgebra.CirculantHadamard.OrderSquareEven
import OAI.LinearAlgebra.CirculantHadamard.TwoAdicDecomposition
import OAI.LinearAlgebra.CirculantHadamard.OrderProjection
import OAI.LinearAlgebra.CirculantHadamard.OrderDescent

namespace OAI

/-!
# The order of an actual circulant sign Hadamard matrix

The matrix supplies its literal integer sign row. Its positive even square
order has a two-adic decomposition. Projecting the actual row gives odd
coefficients, and the proved cyclotomic halving descent excludes every
two-adic exponent except two, without any coefficient-divisibility or descent
assumption.
-/

namespace CirculantHadamard

/-- Every nontrivial actual real circulant sign Hadamard matrix has order
`4 * u^2` for a positive odd natural number `u`. -/
theorem order_reduction {n : ℕ} (hn : 1 < n)
    (h : ExistsRealCirculantHadamard n) :
    ∃ u : ℕ, 0 < u ∧ Odd u ∧ n = 4 * u ^ 2 := by
  let : NeZero n := ⟨by omega⟩
  obtain ⟨hsquare, heven⟩ := order_square_even hn h
  obtain ⟨s, u, hs, huPos, hu, horder⟩ :=
    exists_two_adic_square_decomposition_of_positive_square hsquare heven
  obtain ⟨f, hf, hnorm⟩ := (exists_cyclicSignRow_iff_real (n := n)).2 h
  have hsOne : s = 1 := by
    by_contra hsOne
    have hsTwo : 2 ≤ s := by omega
    obtain ⟨T, hodd, hTnorm⟩ :=
      exists_odd_cyclic_projection hu horder f hf hnorm
    exact odd_norm_impossible (by omega : 1 ≤ s) (by omega : s + 2 ≤ 2 * s)
      hu T hodd hTnorm
  refine ⟨u, huPos, hu, ?_⟩
  simpa [hsOne] using horder

/-- The order restriction stated directly for the supplied real matrix. -/
theorem order_reduction_of_matrix {n : ℕ} (hn : 1 < n) (H : RealMatrix n)
    (hc : IsCirculant H) (hh : IsSignHadamard H) :
    ∃ u : ℕ, 0 < u ∧ Odd u ∧ n = 4 * u ^ 2 :=
  order_reduction hn ⟨H, hc, hh⟩

end CirculantHadamard

end OAI
