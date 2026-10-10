import OAI.NumberTheory.Ostmann.Construction.InitialLogSumRate

namespace OAI

/-! # Initial logarithmic cutoffs on the support of the original priors -/

namespace Ostmann
open scoped Classical BigOperators

/-- The score only needs to be bounded where its weight is nonzero. This
allows all prime roles to share the same large ambient container. -/
theorem exists_supported_log_sum_center {A : Type*} [Fintype A]
    (weight score : A → ℝ) (N : ℕ) (β : ℝ)
    (hmass : β ≤ ∑ a, weight a)
    (hscore : ∀ a, weight a ≠ 0 → 0 ≤ score a ∧ score a ≤ N) :
    ∃ c ∈ Finset.Icc (0 : ℤ) N,
      β / (N + 1) ≤ ∑ a, weight a * logCellProfile (score a - c) := by
  let score' : A → ℝ := fun a => if weight a = 0 then 0 else score a
  have hs (a : A) : 0 ≤ score' a ∧ score' a ≤ N := by
    by_cases ha : weight a = 0
    · simp only [score', ite_eq_left ha]
      exact ⟨le_rfl, Nat.cast_nonneg _⟩
    · simpa only [score', ite_eq_right ha] using hscore a ha
  obtain ⟨c, hc, h⟩ := exists_weighted_log_sum_center weight score' N β hmass hs
  refine ⟨c, hc, ?_⟩
  convert h using 1
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : weight a = 0
  · simp only [ha, zero_mul]
  · simp only [score', ite_eq_right ha]

theorem exists_supported_balanced_log_sum_center {A : Type*} [Fintype A]
    (n : ℕ) (μ : Fin n → A → ℝ) (good : Fin n → A → Prop)
    (score : (Fin n → A) → ℝ) (N : ℕ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hmass : ∀ i, δ ≤ ∑ a, if good i a then μ i a else 0)
    (hscore : ∀ x, productPrior μ x ≠ 0 → 0 ≤ score x ∧ score x ≤ N) :
    ∃ c ∈ Finset.Icc (0 : ℤ) N,
      δ ^ n / (N + 1) ≤ ∑ x ∈ balancedTupleSet n good,
        productPrior μ x * logCellProfile (score x - c) := by
  have hb := balancedTupleSet_mass n μ good δ hδ hmass
  have hm : δ ^ n ≤ ∑ x, if ∀ i, good i (x i) then productPrior μ x else 0 := by
    simpa only [balancedTupleSet, Finset.sum_filter] using hb
  obtain ⟨c, hc, h⟩ := exists_supported_log_sum_center
    (fun x => if ∀ i, good i (x i) then productPrior μ x else 0) score N (δ ^ n) hm (by
      intro x hx
      have hprod : productPrior μ x ≠ 0 := by
        intro he
        by_cases hg : ∀ i, good i (x i) <;> simp [hg, he] at hx
      exact hscore x hprod)
  refine ⟨c, hc, ?_⟩
  simpa only [balancedTupleSet, Finset.sum_filter, ite_mul, zero_mul] using h

/-- The cutoff remains in the true bulk or spectator range although its
prior is represented on a container that also contains the giant primes. -/
theorem exists_supported_prime_log_sum_center (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (n m : ℕ) (T : ℝ)
    (μ : Fin n → P → ℝ) (good : Fin n → P → Prop)
    (hm : 1 ≤ m) (hn : n ≤ m) (hT : T ≤ m)
    (hlog : ∀ i (p : P), μ i p ≠ 0 → Real.log (p : ℝ) ≤ Real.exp T)
    (hmass : ∀ i, (1 / 2 : ℝ) ≤ ∑ p, if good i p then μ i p else 0) :
    ∃ c ∈ Finset.Icc (0 : ℤ) ⌈(n : ℝ) * Real.exp T⌉₊,
      Real.exp (-(Real.log 2 + 2) * m) ≤
        ∑ x ∈ balancedTupleSet n good, productPrior μ x *
          logCellProfile ((∑ i, Real.log (x i : ℝ)) - c) := by
  have hscore (x : Fin n → P) (hx : productPrior μ x ≠ 0) :
      0 ≤ ∑ i, Real.log (x i : ℝ) ∧
        (∑ i, Real.log (x i : ℝ)) ≤ (⌈(n : ℝ) * Real.exp T⌉₊ : ℝ) := by
    constructor
    · exact Finset.sum_nonneg fun i _ => Real.log_nonneg
        (by exact_mod_cast (hP (x i) (x i).property).one_lt.le)
    · calc
        _ ≤ ∑ _i : Fin n, Real.exp T := by
          apply Finset.sum_le_sum
          intro i hi
          apply hlog i (x i)
          intro hz
          apply hx
          exact Finset.prod_eq_zero hi hz
        _ = (n : ℝ) * Real.exp T := by simp
        _ ≤ _ := Nat.le_ceil _
  obtain ⟨c, hc, h⟩ := exists_supported_balanced_log_sum_center n μ good
    (fun x => ∑ i, Real.log (x i : ℝ)) ⌈(n : ℝ) * Real.exp T⌉₊
    (1 / 2) (by norm_num) hmass hscore
  exact ⟨c, hc, (halfPower_div_logSumCenters n m T hm hn hT).trans h⟩

end Ostmann

end OAI
