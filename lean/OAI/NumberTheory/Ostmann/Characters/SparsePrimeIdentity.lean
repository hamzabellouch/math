import OAI.NumberTheory.Ostmann.Characters.SparseIntegerExpansion
import OAI.NumberTheory.Ostmann.Characters.CharacterPrimeMean
import OAI.NumberTheory.Ostmann.Supply.NonnegativeSparseWeight

namespace OAI

/-! # The primitive expansion agrees with the original weight on the supported primes -/
namespace Ostmann
open scoped Classical BigOperators

 theorem supported_prime_coprime {n : ℕ} (p : Fin n → ℕ) [∀ i, Fact (p i).Prime]
    (X : ℝ) (hX : 0 < X) (hp : ∀ i, (p i : ℝ) ≤ X / 2)
    (q : ℕ) (hq : q.Prime) (ht : primeMeanTest (q / X) ≠ 0) :
    q.Coprime (∏ i, p i) := by
  have hmem : (q : ℝ) / X ∈ Set.Icc (5 / 8 : ℝ) (7 / 8) := by
    by_contra h
    exact ht (primeMeanTest_zero_outside _ h)
  have hqX := (le_div_iff₀ hX).mp hmem.1
  apply Nat.coprime_prod_right_iff.mpr
  intro i _
  apply (Nat.coprime_primes hq (Fact.out : (p i).Prime)).mpr
  intro he
  have hh := hp i
  rw [← he] at hh
  linarith

 theorem sparsePrimeSum_identity {n : ℕ} (p : Fin n → ℕ)
    [∀ i, Fact (p i).Prime] [NeZero (∏ i, p i)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) (K : ℕ)
    (X : ℝ) (hX : 0 < X) (hp : ∀ i, (p i : ℝ) ≤ X / 2) :
    let E := fun i => largeTransformSpectrum (normalizedResidueTransform (S i))
    smoothPrimeSum (primitiveCharacterPolynomial
      (sparsePrimitiveSupport p E (17 / 20) K).eraseNone
      (fun ρ => sparsePrimitiveCoefficient p E (17 / 20) K (some ρ))
      (sparsePrimitiveCoefficient p E (17 / 20) K none)) X =
    ((∑ q ∈ (Finset.Ioc 0 ⌊X⌋₊).filter Nat.Prime,
      Real.log q * sparseSubsetWeight p S K (fun i => (q : ZMod (p i))) *
        primeMeanTest (q / X) : ℝ) : ℂ) := by
  intro E
  simp only [smoothPrimeSum, Complex.ofReal_sum, Complex.ofReal_mul]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases ht : primeMeanTest (q / X) = 0
  · simp only [ht, Complex.ofReal_zero, mul_zero]
  · have hh := sparseWeight_integer_expansion p hc E (17 / 20) K q
      (supported_prime_coprime p X hX hp q (Finset.mem_filter.mp hq).2 ht)
    have hw := sparseSubsetWeight_complex p S K (fun i => (q : ZMod (p i)))
    change (sparseSubsetWeight p S K (fun i => (q : ZMod (p i))) : ℂ) =
      elementaryTruncation (fun i => sparseAdditiveKernel (E i) (17 / 20) (q : ZMod (p i))) K ^ 2 at hw
    rw [hw, hh]
    rfl

end Ostmann

end OAI
