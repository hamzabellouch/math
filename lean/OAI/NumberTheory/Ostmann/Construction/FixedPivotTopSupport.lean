import OAI.NumberTheory.Ostmann.Construction.FiniteTopSupport
import OAI.NumberTheory.Ostmann.Construction.PrimeWordCoefficient
import OAI.NumberTheory.Ostmann.Construction.FixedPivotPrimeChecks

namespace OAI

/-! # Top collisions and external integers in the supported history pair -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical SchwartzMap

theorem fixed_pivot_top_prime_coefficient_pair_bound
    {A J : Type*} [Fintype A] [Nonempty A] [Fintype J] {K : Type*} [Fintype K] [Nonempty K] {n : ℕ}
    (prime : A → ℕ) (hpInj : Function.Injective prime) (hprime : ∀ a, (prime a).Prime)
    (checks : J → TopPrimeCondition (K))
    (C C' : WordPrimeDecoration (Option (K)) n)
    (U U' D D' : WordRangeDecoration (ExpandedScheduledVariable (Option (K)) n) n)
    (template template' : WordTransferTemplate (ExpandedScheduledVariable (Option (K)) n) n)
    (t t' : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (ht' : NonzeroInternalFrequencies n t')
    (p p' : WordFourierParameters n)
    (μ : K → A → ℝ) (hμ : ∀ i a, 0 ≤ μ i a) (hmass : ∀ i, ∑ a, μ i a = 1)
    (α V R : ℝ) (hα : 0 ≤ α) (hV : 0 < V) (hR : 3 ≤ R)
    (hmax : ∀ i a, μ i a ≤ α)
    (hlower : ∀ a, V ≤ Real.log (prime a : ℝ)) (hupper : ∀ a, (prime a : ℝ) ≤ R)
    (hbound : ∀ j, (checks j).Bounded R)
    (M : ℕ) (G : (Option (K) → ℕ) → ℂ) (hG : ∀ x, ‖G x‖ ≤ 1)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hcancel : ‖∑ x, (finiteProductPrior μ x : ℂ) *
      (G (fixedPivotPrimeValues M (fun i => prime (x i))) *
        (p.primeUnitRangedCoefficient C U D template t ht (fixedPivotPrimeValues M (fun i => prime (x i))) *
        conj (p'.primeUnitRangedCoefficient C' U' D' template' t' ht' (fixedPivotPrimeValues M (fun i => prime (x i))))))‖ ≤ δ) :
    ‖∑ x, (finiteProductPrior μ x : ℂ) *
      (if ∀ j, (checks j).Holds (fun i => prime (x i)) then
        G (fixedPivotPrimeValues M (fun i => prime (x i))) *
          (p.primeUnitRangedCoefficient C U D template t ht (fixedPivotPrimeValues M (fun i => prime (x i))) *
          conj (p'.primeUnitRangedCoefficient C' U' D' template' t' ht' (fixedPivotPrimeValues M (fun i => prime (x i)))))
        else 0)‖ ≤
      δ + ((SchwartzMap.seminorm ℝ 0 0 p.profile) ^ (2 ^ n) *
        (SchwartzMap.seminorm ℝ 0 0 p'.profile) ^ (2 ^ n)) *
        (Fintype.card J : ℝ) * (α + Real.log R / V * α) := by
  let B := (SchwartzMap.seminorm ℝ 0 0 p.profile) ^ (2 ^ n) *
    (SchwartzMap.seminorm ℝ 0 0 p'.profile) ^ (2 ^ n)
  have hp0 : 0 ≤ (SchwartzMap.seminorm ℝ 0 0 p.profile) ^ (2 ^ n) :=
    pow_nonneg ((norm_nonneg (p.profile 0)).trans (p.profile.norm_le_seminorm ℝ 0)) _
  have hp'0 : 0 ≤ (SchwartzMap.seminorm ℝ 0 0 p'.profile) ^ (2 ^ n) :=
    pow_nonneg ((norm_nonneg (p'.profile 0)).trans (p'.profile.norm_le_seminorm ℝ 0)) _
  apply finite_top_prime_support_bound prime hpInj hprime checks μ hμ hmass α V R
    hα hV hR hmax hlower hupper hbound _ B δ (mul_nonneg hp0 hp'0) hδ _ hcancel
  intro x
  rw [norm_mul, norm_mul, Complex.norm_conj]
  have hprod := mul_le_mul
    (p.primeUnitRangedCoefficient_norm C U D template t ht (fixedPivotPrimeValues M (fun i => prime (x i))))
    (p'.primeUnitRangedCoefficient_norm C' U' D' template' t' ht' (fixedPivotPrimeValues M (fun i => prime (x i))))
    (norm_nonneg _) hp0
  exact (mul_le_mul (hG _) hprod (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (by norm_num)).trans_eq (one_mul B)

end Ostmann

end OAI
