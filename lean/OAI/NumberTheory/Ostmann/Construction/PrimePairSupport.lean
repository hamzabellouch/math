import OAI.NumberTheory.Ostmann.Construction.WordPrimeCheckBound

namespace OAI

/-! # Both histories retain their large-prime support under the original law -/

namespace Ostmann

open scoped BigOperators Classical

theorem word_prime_pair_checks_bound
    {A : Type*} [Fintype A] [Nonempty A] {m n : ℕ}
    (prime : A → ℕ) (hpInj : Function.Injective prime) (hprime : ∀ a, (prime a).Prime)
    (D D' : WordPrimeDecoration (Fin (m + 1)) n)
    (template template' : WordTransferTemplate (ExpandedScheduledVariable (Fin (m + 1)) n) n)
    (t t' : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (ht' : NonzeroInternalFrequencies n t')
    (B : ℕ) (hB : 1 ≤ B) (hwords : template.WordsBounded B) (hwords' : template'.WordsBounded B)
    (μ : Fin (m + 1) → A → ℝ) (hμ : ∀ i a, 0 ≤ μ i a) (hmass : ∀ i, ∑ a, μ i a = 1)
    (α β V R : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hV : 0 < V) (hR : 3 ≤ R)
    (hmax : ∀ i a, μ i a ≤ α) (hpmax : ∀ i a, μ i a ≤ β)
    (hlower : ∀ a, V ≤ Real.log (prime a : ℝ)) (hupper : ∀ a, (prime a : ℝ) ≤ R)
    (hfreq : ∀ s ∈ allFrequencyList n t, |(s : ℝ)| ≤ R)
    (hfreq' : ∀ s ∈ allFrequencyList n t', |(s : ℝ)| ≤ R)
    (hsmall : ∀ a, ∀ s ∈ allFrequencyList n t, 0 < s.natAbs ∧ s.natAbs < prime a)
    (hsmall' : ∀ a, ∀ s ∈ allFrequencyList n t', 0 < s.natAbs ∧ s.natAbs < prime a)
    (W : (Fin (m + 1) → A) → ℂ) (C δ : ℝ)
    (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hW : ∀ x, ‖W x‖ ≤ C)
    (hvalid : ∀ x, W x ≠ 0 → ValidTransferHistory
      (wordTransferSystem (ExpandedScheduledVariable (Fin (m + 1)) n)) n
      (template.state (expandedPrimeNatValues n (fun i => prime (x i)))) t)
    (hvalid' : ∀ x, W x ≠ 0 → ValidTransferHistory
      (wordTransferSystem (ExpandedScheduledVariable (Fin (m + 1)) n)) n
      (template'.state (expandedPrimeNatValues n (fun i => prime (x i)))) t')
    (hcancel : ‖∑ x, (productPrior μ x : ℂ) * W x‖ ≤ δ) :
    ‖∑ x, (productPrior μ x : ℂ) *
      (if (∀ g ∈ D.checks template t ht .prime,
          g.Holds (expandedPrimeValues n (fun i => (prime (x i) : ℤ))) (fun i => prime (x i))) ∧
        (∀ g ∈ D'.checks template' t' ht' .prime,
          g.Holds (expandedPrimeValues n (fun i => (prime (x i) : ℤ))) (fun i => prime (x i)))
        then W x else 0)‖ ≤
      δ + C * ((D.count + D'.count : ℕ) : ℝ) * (B ^ (n + 1) : ℕ) * (α + Real.log R / V * β) := by
  let good := fun x : Fin (m + 1) → A => ∀ g ∈ D.checks template t ht .prime,
    g.Holds (expandedPrimeValues n (fun i => (prime (x i) : ℤ))) (fun i => prime (x i))
  let W₁ := fun x => if good x then W x else 0
  let E := C * (D.count : ℝ) * (B ^ (n + 1) : ℕ) * (α + Real.log R / V * β)
  have hE : 0 ≤ E := by
    apply mul_nonneg
    · positivity
    · exact add_nonneg hα (mul_nonneg (div_nonneg (Real.log_nonneg (by linarith)) hV.le) hβ)
  have hfirst : ‖∑ x, (productPrior μ x : ℂ) * W₁ x‖ ≤ δ + E :=
    word_prime_checks_bound prime hpInj hprime D template t ht B hB hwords μ hμ hmass
      α β V R hα hβ hV hR hmax hpmax hlower hupper hfreq hsmall W C δ hC hδ hW hvalid hcancel
  have hW₁ (x) : ‖W₁ x‖ ≤ C := by
    dsimp only [W₁]
    split_ifs
    · exact hW x
    · simpa only [norm_zero] using hC
  have hWne (x) (hx : W₁ x ≠ 0) : W x ≠ 0 := by
    intro hw
    apply hx
    simp only [W₁, hw, ite_self]
  have hsecond := word_prime_checks_bound prime hpInj hprime D' template' t' ht' B hB hwords'
    μ hμ hmass α β V R hα hβ hV hR hmax hpmax hlower hupper hfreq' hsmall'
    W₁ C (δ + E) hC (add_nonneg hδ hE) hW₁ (fun x hx => hvalid' x (hWne x hx)) hfirst
  have he (x : Fin (m + 1) → A) :
      (if ∀ g ∈ D'.checks template' t' ht' .prime,
        g.Holds (expandedPrimeValues n (fun i => (prime (x i) : ℤ))) (fun i => prime (x i))
        then W₁ x else 0) =
      (if (∀ g ∈ D.checks template t ht .prime,
          g.Holds (expandedPrimeValues n (fun i => (prime (x i) : ℤ))) (fun i => prime (x i))) ∧
        (∀ g ∈ D'.checks template' t' ht' .prime,
          g.Holds (expandedPrimeValues n (fun i => (prime (x i) : ℤ))) (fun i => prime (x i)))
        then W x else 0) := by
    dsimp only [W₁, good]
    split_ifs <;> simp_all
  simp_rw [he] at hsecond
  apply hsecond.trans_eq
  dsimp only [E]
  push_cast
  ring

end Ostmann

end OAI
