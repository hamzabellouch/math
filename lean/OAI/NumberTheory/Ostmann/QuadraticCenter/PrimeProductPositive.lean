import OAI.NumberTheory.Ostmann.QuadraticCenter.AmplifiedPositive
import OAI.NumberTheory.Ostmann.QuadraticCenter.PrimeProductMeanLower

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem primeProductSamples_poisson_data {P : Finset ℕ}
    (hP : ∀ r ∈ P, Nat.Prime r) (ho : ∀ r ∈ P, Odd r)
    {L k q : ℕ} (hc : ∀ r ∈ P, r.Coprime L) (hk : 0 < k)
    (hq : q ∈ primeProductSamples P k) :
    Squarefree q ∧ Odd q ∧ 1 < q ∧ q.Coprime L := by
  classical
  have hd := primeProductSamples_properties hP ho
    (H := P.sup id) (fun r hr => Finset.le_sup (f := id) hr) hq
  refine ⟨hd.1, hd.2.1, ?_, ?_⟩
  · have hn : q ≠ 0 := hd.1.ne_zero
    by_contra h
    have he : q = 1 := by omega
    have hh := hd.2.2.2
    simp [he] at hh
    omega
  · obtain ⟨U, hU, rfl⟩ := Finset.mem_image.mp hq
    exact Nat.Coprime.prod_left (fun r hr => hc r r.property)

def primeProductPositive {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)] [NeZero (∏ i, p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) (lam X : ℝ) (t : ℕ → ℤ) (q : ℕ) : ℂ :=
  ∑' n : ℕ, amplifierFrequency p hcop S lam q X
    ((primeProductCenter q t : ℝ) / q +
      centerCorrection q (∏ i, p i) (primeProductCenter q t)) ((n : ℤ) + 1)

theorem primeProductTransform_le_positive {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)] [NeZero (∏ i, p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) (lam : ℝ) {X : ℝ} (hX : 0 < X)
    (t : ℕ → ℤ) {q : ℕ} (hsq : Squarefree q) (ho : Odd q) (hq : 1 < q)
    (hc : q.Coprime (∏ i, p i)) :
    ‖primeProductTransform p hcop S lam X t q‖ / Real.sqrt X ≤
      2 * ‖primeProductPositive p hcop S lam X t q‖ := by
  let : NeZero q := ⟨by omega⟩
  simpa only [primeProductTransform, primeProductPositive, Int.cast_natCast] using
    amplified_transform_two_positive p hcop S lam hc ho hsq hq hX (primeProductCenter q t)

theorem primeProductMean_mono (P : Finset ℕ) (k : ℕ) {f g : ℕ → ℝ}
    (hfg : ∀ q ∈ primeProductSamples P k, f q ≤ g q) :
    primeProductMean P k f ≤ primeProductMean P k g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum hfg) (Nat.cast_nonneg _)

theorem primeProductMean_const_mul (P : Finset ℕ) (k : ℕ) (c : ℝ) (f : ℕ → ℝ) :
    primeProductMean P k (fun q => c * f q) = c * primeProductMean P k f := by
  simp only [primeProductMean, ← Finset.mul_sum, mul_div_assoc]

theorem primeProductMean_div_const (P : Finset ℕ) (k : ℕ) (f : ℕ → ℝ) (c : ℝ) :
    primeProductMean P k (fun q => f q / c) = primeProductMean P k f / c := by
  unfold primeProductMean
  rw [← Finset.sum_div]
  ring

theorem amplified_distinct_le_positive_mean {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)] [NeZero (∏ i, p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) {lam X : ℝ}
    (hlam : 0 ≤ lam) (hlam1 : lam < 1) (hX : 0 < X)
    (P : Finset ℕ) (hP : ∀ r ∈ P, Nat.Prime r) (ho : ∀ r ∈ P, Odd r)
    (hc : ∀ r ∈ P, r.Coprime (∏ i, p i)) (hJ : 0 < P.card)
    (ε t : ℕ → ℤ) (hε : ∀ r ∈ P, ε r = -1 ∨ ε r = 1)
    {k : ℕ} (hk : 0 < k) (hkJ : k ≤ P.card) :
    (∑' n : ℤ, amplifierWeight p hcop S lam X n *
      distinctSignAverage P (fun r => ε r * jacobiSym (n - t r) r) k) / Real.sqrt X ≤
      2 * primeProductMean P k (fun q => ‖primeProductPositive p hcop S lam X t q‖) := by
  apply (div_le_div_of_nonneg_right
    (amplified_distinct_le_product_mean p hcop S hlam hlam1 hX P hP hJ ε t hε hkJ)
    (Real.sqrt_nonneg X)).trans
  rw [← primeProductMean_div_const, ← primeProductMean_const_mul]
  apply primeProductMean_mono
  intro q hq
  obtain ⟨hsq, hodd, hq1, hcopq⟩ := primeProductSamples_poisson_data hP ho hc hk hq
  exact primeProductTransform_le_positive p hcop S lam hX t hsq hodd hq1 hcopq

end Ostmann.QuadraticCenter

end

end OAI
