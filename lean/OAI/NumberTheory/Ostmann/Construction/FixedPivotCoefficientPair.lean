import OAI.NumberTheory.Ostmann.Construction.PrimeWordCoefficient
import OAI.NumberTheory.Ostmann.Construction.FixedPivotPairSupport

namespace OAI

/-! # Large-prime support in the actual two-history coefficient estimate -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical SchwartzMap

theorem fixed_pivot_prime_coefficient_pair_bound
    {A : Type*} [Fintype A] [Nonempty A] {K : Type*} [Fintype K] [Nonempty K] {n : ℕ}
    (prime : A → ℕ) (hpInj : Function.Injective prime) (hprime : ∀ a, (prime a).Prime)
    (C C' : WordPrimeDecoration (Option (K)) n)
    (U U' D D' : WordRangeDecoration (ExpandedScheduledVariable (Option (K)) n) n)
    (template template' : WordTransferTemplate (ExpandedScheduledVariable (Option (K)) n) n)
    (t t' : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (ht' : NonzeroInternalFrequencies n t')
    (hC : C.Coordinates (· ≠ none)) (hC' : C'.Coordinates (· ≠ none))
    (B : ℕ) (hB : 1 ≤ B) (hwords : template.WordsBounded B) (hwords' : template'.WordsBounded B)
    (p p' : WordFourierParameters n)
    (μ : K → A → ℝ) (hμ : ∀ i a, 0 ≤ μ i a) (hmass : ∀ i, ∑ a, μ i a = 1)
    (α β V R : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hV : 0 < V) (hR : 3 ≤ R)
    (M : ℕ) (hM : (M : ℝ) ≤ R)
    (hmax : ∀ i a, μ i a ≤ α) (hpmax : ∀ i a, μ i a ≤ β)
    (hlower : ∀ a, V ≤ Real.log (prime a : ℝ)) (hupper : ∀ a, (prime a : ℝ) ≤ R)
    (hfreq : ∀ s ∈ allFrequencyList n t, |(s : ℝ)| ≤ R)
    (hfreq' : ∀ s ∈ allFrequencyList n t', |(s : ℝ)| ≤ R)
    (hsmall : ∀ a, ∀ s ∈ allFrequencyList n t, 0 < s.natAbs ∧ s.natAbs < prime a)
    (hsmall' : ∀ a, ∀ s ∈ allFrequencyList n t', 0 < s.natAbs ∧ s.natAbs < prime a)
    (G : (Option (K) → ℕ) → ℂ) (hG : ∀ x, ‖G x‖ ≤ 1)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hcancel : ‖∑ x, (finiteProductPrior μ x : ℂ) *
      (G (fixedPivotPrimeValues M (fun i => prime (x i))) *
        (p.unitRangedCoefficient U D template t ht
          (expandedPrimeValues n (fun i => (fixedPivotPrimeValues M (fun j => prime (x j)) i : ℤ))) *
        conj (p'.unitRangedCoefficient U' D' template' t' ht'
          (expandedPrimeValues n (fun i => (fixedPivotPrimeValues M (fun j => prime (x j)) i : ℤ))))))‖ ≤ δ) :
    ‖∑ x, (finiteProductPrior μ x : ℂ) *
      (G (fixedPivotPrimeValues M (fun i => prime (x i))) *
        (p.primeUnitRangedCoefficient C U D template t ht (fixedPivotPrimeValues M (fun i => prime (x i))) *
        conj (p'.primeUnitRangedCoefficient C' U' D' template' t' ht' (fixedPivotPrimeValues M (fun i => prime (x i))))))‖ ≤
      δ + ((SchwartzMap.seminorm ℝ 0 0 p.profile) ^ (2 ^ n) *
        (SchwartzMap.seminorm ℝ 0 0 p'.profile) ^ (2 ^ n)) *
        ((C.count + C'.count : ℕ) : ℝ) * (B ^ (n + 1) : ℕ) * (α + Real.log R / V * β) := by
  let a := fun x : K → A => expandedPrimeValues n (fun i => (fixedPivotPrimeValues M (fun j => prime (x j)) i : ℤ))
  let f := fun x => p.unitRangedCoefficient U D template t ht (a x)
  let f' := fun x => p'.unitRangedCoefficient U' D' template' t' ht' (a x)
  let W := fun x => G (fixedPivotPrimeValues M (fun i => prime (x i))) * (f x * conj (f' x))
  let N := (SchwartzMap.seminorm ℝ 0 0 p.profile) ^ (2 ^ n) *
    (SchwartzMap.seminorm ℝ 0 0 p'.profile) ^ (2 ^ n)
  have hp0 : 0 ≤ (SchwartzMap.seminorm ℝ 0 0 p.profile) ^ (2 ^ n) :=
    pow_nonneg ((norm_nonneg (p.profile 0)).trans (p.profile.norm_le_seminorm ℝ 0)) _
  have hp'0 : 0 ≤ (SchwartzMap.seminorm ℝ 0 0 p'.profile) ^ (2 ^ n) :=
    pow_nonneg ((norm_nonneg (p'.profile 0)).trans (p'.profile.norm_le_seminorm ℝ 0)) _
  have hN : 0 ≤ N := mul_nonneg hp0 hp'0
  have hW (x) : ‖W x‖ ≤ N := by
    dsimp only [W]
    rw [norm_mul, norm_mul, Complex.norm_conj]
    have hff : ‖f x‖ * ‖f' x‖ ≤ N := mul_le_mul
      (p.unitRangedCoefficient_norm U D template t ht (a x))
      (p'.unitRangedCoefficient_norm U' D' template' t' ht' (a x)) (norm_nonneg _) hp0
    exact (mul_le_mul (hG _) hff (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (by norm_num)).trans_eq (one_mul N)
  have hv (x) (hx : W x ≠ 0) : ValidTransferHistory
      (wordTransferSystem (ExpandedScheduledVariable (Option (K)) n)) n
      (template.state (expandedPrimeNatValues n (fixedPivotPrimeValues M (fun i => prime (x i))))) t := by
    apply p.unitRangedCoefficient_valid U D template t ht
    rw [expandedPrimeNatValues_cast]
    intro hf
    apply hx
    simp only [W, f, a, hf, zero_mul, mul_zero]
  have hv' (x) (hx : W x ≠ 0) : ValidTransferHistory
      (wordTransferSystem (ExpandedScheduledVariable (Option (K)) n)) n
      (template'.state (expandedPrimeNatValues n (fixedPivotPrimeValues M (fun i => prime (x i))))) t' := by
    apply p'.unitRangedCoefficient_valid U' D' template' t' ht'
    rw [expandedPrimeNatValues_cast]
    intro hf
    apply hx
    simp only [W, f', a, hf, map_zero, mul_zero]
  have hh := word_prime_pair_checks_fixed_pivot_bound prime hpInj hprime C C' template template' t t' ht ht' hC hC'
    B hB hwords hwords' μ hμ hmass α β V R hα hβ hV hR M hM hmax hpmax hlower hupper
    hfreq hfreq' hsmall hsmall' W N δ hN hδ hW hv hv' hcancel
  have he (x : K → A) :
      (if (∀ g ∈ C.checks template t ht .prime, g.Holds (a x) (fixedPivotPrimeValues M (fun i => prime (x i)))) ∧
        (∀ g ∈ C'.checks template' t' ht' .prime, g.Holds (a x) (fixedPivotPrimeValues M (fun i => prime (x i))))
        then W x else 0) =
      G (fixedPivotPrimeValues M (fun i => prime (x i))) *
        (p.primeUnitRangedCoefficient C U D template t ht (fixedPivotPrimeValues M (fun i => prime (x i))) *
          conj (p'.primeUnitRangedCoefficient C' U' D' template' t' ht' (fixedPivotPrimeValues M (fun i => prime (x i))))) := by
    unfold WordFourierParameters.primeUnitRangedCoefficient
    simp only [W, f, f', a]
    split_ifs <;> simp_all
  change ‖∑ x, (finiteProductPrior μ x : ℂ) *
    (if (∀ g ∈ C.checks template t ht .prime, g.Holds (a x) (fixedPivotPrimeValues M (fun i => prime (x i)))) ∧
      (∀ g ∈ C'.checks template' t' ht' .prime, g.Holds (a x) (fixedPivotPrimeValues M (fun i => prime (x i))))
      then W x else 0)‖ ≤ _ at hh
  simp only [he] at hh
  exact hh

end Ostmann

end OAI
