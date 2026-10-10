import OAI.NumberTheory.Ostmann.QuadraticCenter.AmplifiedDistinctLower
import OAI.NumberTheory.Ostmann.QuadraticCenter.PrimeProductReindex
import OAI.NumberTheory.Ostmann.QuadraticCenter.PrimeProductTransform

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem amplified_distinct_le_product_mean {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) {lam X : ℝ}
    (hlam : 0 ≤ lam) (hlam1 : lam < 1) (hX : 0 < X)
    (P : Finset ℕ) (hP : ∀ r ∈ P, Nat.Prime r) (hJ : 0 < P.card)
    (ε t : ℕ → ℤ) (hε : ∀ r ∈ P, ε r = -1 ∨ ε r = 1)
    {k : ℕ} (hk : k ≤ P.card) :
    (∑' n : ℤ, amplifierWeight p hcop S lam X n *
      distinctSignAverage P (fun r => ε r * jacobiSym (n - t r) r) k) ≤
      primeProductMean P k (fun q => ‖primeProductTransform p hcop S lam X t q‖) := by
  exact (amplified_distinct_le_product_transforms p hcop S hlam hlam1 hX P hP ε t hε k).trans
    (normalized_subset_sum_le_primeProductMean hP hJ hk _ (fun _ => norm_nonneg _))

theorem amplified_moment_le_twice_product_mean {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) {lam X : ℝ}
    (hlam : 0 ≤ lam) (hlam1 : lam < 1) (hX : 0 < X)
    (P : Finset ℕ) (hP : ∀ r ∈ P, Nat.Prime r) (hJ : 0 < P.card)
    (ε t : ℕ → ℤ) (hε : ∀ r ∈ P, ε r = -1 ∨ ε r = 1)
    {k : ℕ} (hk : 2 ≤ k) (hkJ : k ≤ P.card) (heven : Even k) {τ : ℝ} (hτ : 0 < τ)
    (hmass : (∑' n : ℤ, amplifierWeight p hcop S lam X n) * τ ^ k ≤
      ∑' n : ℤ, amplifiedMomentTerm p hcop S lam X P ε t k n)
    (hsmall : 4 * ((((k : ℝ) + 1) * (k : ℝ) ^ 2 / P.card) *
      (τ + (k : ℝ) / Real.sqrt (P.card : ℝ)) ^ (k - 2)) ≤ τ ^ k) :
    (∑' n : ℤ, amplifiedMomentTerm p hcop S lam X P ε t k n) / 2 ≤
      primeProductMean P k (fun q => ‖primeProductTransform p hcop S lam X t q‖) := by
  exact (amplified_distinct_moment_retains_half p hcop S hlam hlam1 hX P hJ ε t hε
    hk heven hτ hmass hsmall).trans
    (amplified_distinct_le_product_mean p hcop S hlam hlam1 hX P hP hJ ε t hε hkJ)

end Ostmann.QuadraticCenter

end

end OAI
