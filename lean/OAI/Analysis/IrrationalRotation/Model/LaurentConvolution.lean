import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Int.Interval

namespace OAI

noncomputable section

namespace Invariant233.FiniteWindow

def laurent (K : ℕ) (a : ℤ → ℂ) : LaurentPolynomial ℂ :=
  ∑ i ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), AddMonoidAlgebra.single i (a i)

def convolution (K : ℕ) (a b : ℤ → ℂ) (n : ℕ) : ℂ :=
  ∑ i ∈ (Finset.Icc (-(K : ℤ)) (K : ℤ)).filter (fun i => |(n : ℤ) + i| ≤ (K : ℤ)),
    a i * b (-(n : ℤ) - i)

end Invariant233.FiniteWindow

end

end OAI
