import OAI.NumberTheory.Ostmann.Construction.PrimeWordCoefficient
import OAI.NumberTheory.Ostmann.Construction.PrimePairSupport

namespace OAI

/-! # Large-prime support in the actual two-history coefficient estimate -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical SchwartzMap

theorem prime_coefficient_pair_bound
    {A : Type*} [Fintype A] [Nonempty A] {m n : ℕ}
    (prime : A → ℕ) (hpInj : Function.Injective prime) (hprime : ∀ a, (prime a).Prime)
    (C C' : WordPrimeDecoration (Fin (m + 1)) n)
    (U U' D D' : WordRangeDecoration (ExpandedScheduledVariable (Fin (m + 1)) n) n)
    (template template' : WordTransferTemplate (ExpandedScheduledVariable (Fin (m + 1)) n) n)
    (t t' : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (ht' : NonzeroInternalFrequencies n t')
    (B : ℕ) (hB : 1 ≤ B) (hwords : template.WordsBounded B) (hwords' : template'.WordsBounded B)
    (p p' : WordFourierParameters n)
    (μ : Fin (m + 1) → A → ℝ) (hμ : ∀ i a, 0 ≤ μ i a) (hmass : ∀ i, ∑ a, μ i a = 1)
    (α β V R : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hV : 0 < V) (hR : 3 ≤ R)
    (hmax : ∀ i a, μ i a ≤ α) (hpmax : ∀ i a, μ i a ≤ β)
    (hlower : ∀ a, V ≤ Real.log (prime a : ℝ)) (hupper : ∀ a, (prime a : ℝ) ≤ R)
    (hfreq : ∀ s ∈ allFrequencyList n t, |(s : ℝ)| ≤ R)
    (hfreq' : ∀ s ∈ allFrequencyList n t', |(s : ℝ)| ≤ R)
    (hsmall : ∀ a, ∀ s ∈ allFrequencyList n t, 0 < s.natAbs ∧ s.natAbs < prime a)
    (hsmall' : ∀ a, ∀ s ∈ allFrequencyList n t', 0 < s.natAbs ∧ s.natAbs < prime a)
    (G : (Fin (m + 1) → ℕ) → ℂ) (hG : ∀ x, ‖G x‖ ≤ 1)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hcancel : ‖∑ x, (productPrior μ x : ℂ) *
      (G (fun i => prime (x i)) *
        (p.unitRangedCoefficient U D template t ht
          (expandedPrimeValues n (fun i => (prime (x i) : ℤ))) *
        conj (p'.unitRangedCoefficient U' D' template' t' ht'
          (expandedPrimeValues n (fun i => (prime (x i) : ℤ))))))‖ ≤ δ) :
    ‖∑ x, (productPrior μ x : ℂ) *
      (G (fun i => prime (x i)) *
        (p.primeUnitRangedCoefficient C U D template t ht (fun i => prime (x i)) *
        conj (p'.primeUnitRangedCoefficient C' U' D' template' t' ht' (fun i => prime (x i)))))‖ ≤
      δ + ((SchwartzMap.seminorm ℝ 0 0 p.profile) ^ (2 ^ n) *
        (SchwartzMap.seminorm ℝ 0 0 p'.profile) ^ (2 ^ n)) *
        ((C.count + C'.count : ℕ) : ℝ) * (B ^ (n + 1) : ℕ) * (α + Real.log R / V * β) := by
  let a := fun x : Fin (m + 1) → A => expandedPrimeValues n (fun i => (prime (x i) : ℤ))
  let f := fun x => p.unitRangedCoefficient U D template t ht (a x)
  let f' := fun x => p'.unitRangedCoefficient U' D' template' t' ht' (a x)
  let W := fun x => G (fun i => prime (x i)) * (f x * conj (f' x))
  let M := (SchwartzMap.seminorm ℝ 0 0 p.profile) ^ (2 ^ n) *
    (SchwartzMap.seminorm ℝ 0 0 p'.profile) ^ (2 ^ n)
  have hp0 : 0 ≤ (SchwartzMap.seminorm ℝ 0 0 p.profile) ^ (2 ^ n) :=
    pow_nonneg ((norm_nonneg (p.profile 0)).trans (p.profile.norm_le_seminorm ℝ 0)) _
  have hp'0 : 0 ≤ (SchwartzMap.seminorm ℝ 0 0 p'.profile) ^ (2 ^ n) :=
    pow_nonneg ((norm_nonneg (p'.profile 0)).trans (p'.profile.norm_le_seminorm ℝ 0)) _
  have hM : 0 ≤ M := mul_nonneg hp0 hp'0
  have hW (x) : ‖W x‖ ≤ M := by
    dsimp only [W]
    rw [norm_mul, norm_mul, Complex.norm_conj]
    have hff : ‖f x‖ * ‖f' x‖ ≤ M := mul_le_mul
      (p.unitRangedCoefficient_norm U D template t ht (a x))
      (p'.unitRangedCoefficient_norm U' D' template' t' ht' (a x)) (norm_nonneg _) hp0
    exact (mul_le_mul (hG _) hff (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (by norm_num)).trans_eq (one_mul M)
  have hv (x) (hx : W x ≠ 0) : ValidTransferHistory
      (wordTransferSystem (ExpandedScheduledVariable (Fin (m + 1)) n)) n
      (template.state (expandedPrimeNatValues n (fun i => prime (x i)))) t := by
    apply p.unitRangedCoefficient_valid U D template t ht
    rw [expandedPrimeNatValues_cast]
    intro hf
    apply hx
    simp only [W, f, a, hf, zero_mul, mul_zero]
  have hv' (x) (hx : W x ≠ 0) : ValidTransferHistory
      (wordTransferSystem (ExpandedScheduledVariable (Fin (m + 1)) n)) n
      (template'.state (expandedPrimeNatValues n (fun i => prime (x i)))) t' := by
    apply p'.unitRangedCoefficient_valid U' D' template' t' ht'
    rw [expandedPrimeNatValues_cast]
    intro hf
    apply hx
    simp only [W, f', a, hf, map_zero, mul_zero]
  have hh := word_prime_pair_checks_bound prime hpInj hprime C C' template template' t t' ht ht'
    B hB hwords hwords' μ hμ hmass α β V R hα hβ hV hR hmax hpmax hlower hupper
    hfreq hfreq' hsmall hsmall' W M δ hM hδ hW hv hv' hcancel
  have he (x : Fin (m + 1) → A) :
      (if (∀ g ∈ C.checks template t ht .prime, g.Holds (a x) (fun i => prime (x i))) ∧
        (∀ g ∈ C'.checks template' t' ht' .prime, g.Holds (a x) (fun i => prime (x i)))
        then W x else 0) =
      G (fun i => prime (x i)) *
        (p.primeUnitRangedCoefficient C U D template t ht (fun i => prime (x i)) *
          conj (p'.primeUnitRangedCoefficient C' U' D' template' t' ht' (fun i => prime (x i)))) := by
    unfold WordFourierParameters.primeUnitRangedCoefficient
    simp only [W, f, f', a]
    split_ifs <;> simp_all
  change ‖∑ x, (productPrior μ x : ℂ) *
    (if (∀ g ∈ C.checks template t ht .prime, g.Holds (a x) (fun i => prime (x i))) ∧
      (∀ g ∈ C'.checks template' t' ht' .prime, g.Holds (a x) (fun i => prime (x i)))
      then W x else 0)‖ ≤ _ at hh
  simp only [he] at hh
  exact hh

end Ostmann

end OAI
