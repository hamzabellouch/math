import OAI.Analysis.IrrationalRotation.Model.ProductScales

namespace OAI

namespace Invariant233

structure ProductSamplingPowersAt (p : ProductScaleData) (j : ℕ)
    (s : Finset ℕ) : Prop where
  range : ∀ n ∈ s, (p.m j : ℝ) ^ ((7 / 10 : ℝ) * p.m j) / 2 ≤ n ∧
    (n : ℝ) ≤ (p.m j : ℝ) ^ ((7 / 10 : ℝ) * p.m j)
  cardinality : (p.m j : ℝ) ^ ((69 / 100 : ℝ) * p.m j) ≤ (s.card : ℝ)
  positive : ∀ n ∈ s, 0 < n
  separation : ∀ n ∈ s, ∀ n' ∈ s, n ≠ n' → ∀ v v' : ℤ,
    |v| ≤ (p.m j ^ 300 : ℕ) → |v'| ≤ (p.m j ^ 300 : ℕ) →
    (v ≠ 0 ∨ v' ≠ 0) →
    (p.m j * p.K j * p.m j ^ 1000 : ℕ) < |v * (n : ℤ) + v' * (n' : ℤ)|

end Invariant233

end OAI
