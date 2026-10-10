import OAI.NumberTheory.EgyptianFractions.GoldbachSieveRemainder
import OAI.NumberTheory.EgyptianFractions.PrimePairSieveModel

namespace OAI
/-!
A finite, unconditional Selberg upper bound for ordered prime pairs with the
actual Goldbach local density and explicit root-count error. The analytic
estimates for the optimizing weights and denominator are separate tasks.
-/

noncomputable section
open scoped BigOperators

namespace Problem337

/-- The actual Goldbach local density and progression error may be inserted in
the multiplicity-preserving Selberg model. All arithmetic approximation input
has been discharged; the weights are still arbitrary with `w 1 = 1`. -/
theorem goldbach_primePairs_lambdaSquared_bound (N P : ℕ)
    (hN : 2 ∣ N) (hP : Squarefree P) (w : ℕ → ℝ) (hw : w 1 = 1) :
    ((PrimePairSieve.primePairs N).card : ℝ) ≤
      ((N - 1 : ℕ) : ℝ) *
        (∑ d ∈ P.divisors, BoundingSieve.lambdaSquared w d * goldbachSieveDensity N d) +
      (∑ d ∈ P.divisors, |BoundingSieve.lambdaSquared w d| * goldbachSieveRootCount N d) +
      2 * P.primeFactors.card := by
  have hpos : ∀ p : ℕ, p.Prime → p ∣ P → 0 < goldbachSieveDensity N p := by
    intro p hp _
    exact goldbachSieveDensity_prime_pos N p hp
  have hlt : ∀ p : ℕ, p.Prime → p ∣ P → goldbachSieveDensity N p < 1 := by
    intro p hp _
    exact goldbachSieveDensity_prime_lt_one N p hp (fun _ => hN)
  have hb := PrimePairSieve.primePairs_lambdaSquared_bound N P hP
    (goldbachSieveDensity N) (goldbachSieveDensity_isMultiplicative N)
    hpos hlt w hw
  have hcard : (Finset.Icc 1 (N - 1)).card = N - 1 := by simp
  rw [hcard] at hb
  refine hb.trans (add_le_add (add_le_add le_rfl ?_) le_rfl)
  apply Finset.sum_le_sum
  intro d hd
  have hd0 : d ≠ 0 := by
    have hdiv := (Nat.mem_divisors.mp hd).1
    intro hzero
    subst d
    exact hP.ne_zero (by simpa using hdiv)
  let : NeZero d := ⟨hd0⟩
  exact mul_le_mul_of_nonneg_left (goldbach_polynomial_count_density_discrepancy N d)
    (abs_nonneg _)

end Problem337

end

end OAI
