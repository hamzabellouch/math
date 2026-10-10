import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparseBernoulliSubsets

namespace OAI

namespace MetricKMedian.SparseBernoulli
open Finset
variable {n d : ℕ}

def polynomial {m : ℕ} (S : Fin m → Finset (Fin n)) (c : Fin m → ℚ)
    (q : Fin n → Bool) : ℚ := ∑ j, c j*∏ i ∈ S j, flag q i

theorem polynomial_moment {m : ℕ} (p : Fin n → ℚ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (S : Fin m → Finset (Fin n)) (c : Fin m → ℚ) (hS : ∀ j, (S j).card ≤ d) :
    (run (d := d) p hp n).moment (polynomial S c)=∑ j, c j*∏ i ∈ S j, p i := by
  unfold SparseIntegerLaw.moment polynomial
  simp only [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  have hh := subset_moment p hp (S j) (hS j)
  change (run (d := d) p hp n).moment (fun q => c j*∏ i∈S j,flag q i)=_
  rw [SparseIntegerLaw.moment_mul,hh]

end MetricKMedian.SparseBernoulli

end OAI
