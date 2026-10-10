import OAI.NumberTheory.Ostmann.Arithmetic.MovingConstructedLiveProductStep

namespace OAI

/-! # Frequency separation from the live original prime priors -/
namespace Ostmann
open scoped Classical BigOperators

theorem live_prime_product_divisor_large {I P : Type*} [Fintype I]
    (value : P → ℕ) (hvalue : ∀ p, (value p).Prime)
    (ν : I → P → ℝ) (V : ℕ)
    (hlive : ∀ i p, ν i p ≠ 0 → V < value p)
    (y : I → P) (hy : (∏ i, ν i (y i)) ≠ 0)
    (q : ℕ) (hq : q.Prime) (hd : q ∣ ∏ i, value (y i)) : V < q := by
  obtain ⟨i, _, hi⟩ := (hq.prime.dvd_finsetProd_iff _).mp hd
  have he : q = value (y i) := (Nat.dvd_prime (hvalue _)).mp hi |>.resolve_left hq.ne_one
  rw [he]
  exact hlive i (y i) (Finset.prod_ne_zero_iff.mp hy i (Finset.mem_univ _))

theorem live_giant_product_divisor_large {I P : Type*} [Fintype I]
    (value : P → ℕ) (hvalue : ∀ p, (value p).Prime)
    (ν : I → P → ℝ) (V X : ℕ) (hX : X.Prime) (hXV : V < X)
    (hlive : ∀ i p, ν i p ≠ 0 → V < value p)
    (y : I → P) (hy : (∏ i, ν i (y i)) ≠ 0)
    (q : ℕ) (hq : q.Prime) (hd : q ∣ X * ∏ i, value (y i)) : V < q := by
  rcases hq.dvd_mul.mp hd with hd | hd
  · have he : q = X := (Nat.dvd_prime hX).mp hd |>.resolve_left hq.ne_one
    exact he ▸ hXV
  · exact live_prime_product_divisor_large value hvalue ν V hlive y hy q hq hd

end Ostmann

end OAI
