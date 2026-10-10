import Mathlib

namespace OAI

namespace Problem346

/-- A finite sequence of zero-reflecting transitions can be cancelled backwards. -/
theorem eq_zero_of_backward_chain {M : Type*} [Zero M]
    (P : ℕ → M) (m : ℕ)
    (hstep : ∀ k < m, P (k+1) = 0 → P k = 0)
    (hm : P m = 0) : P 0 = 0 := by
  exact Nat.decreasingInduction (motive := fun k _ => P k = 0)
    (fun k hk => hstep k (by omega)) hm (Nat.zero_le m)

/-- Scalar factors in derivative-chain identities need not be divided out when
propagating a zero endpoint backwards. Only zero reflection of each derivative
on its current polynomial is required. -/
theorem eq_zero_of_linear_chain {R M : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M]
    (P : ℕ → M) (D : ℕ → Module.End R M) (c : ℕ → R) (m : ℕ)
    (hchain : ∀ k < m, D k (P k) = c k • P (k+1))
    (hreflect : ∀ k < m, D k (P k) = 0 → P k = 0)
    (hm : P m = 0) : P 0 = 0 := by
  apply eq_zero_of_backward_chain P m _ hm
  intro k hk hz
  apply hreflect k hk
  rw [hchain k hk, hz, smul_zero]

end Problem346

end OAI
