import OAI.NumberTheory.TotientAsymptotic.PublishedComparison
import OAI.NumberTheory.TotientAsymptotic.TupleRecovery

namespace OAI

/-! Counting the residual tuple data forgotten by Ford's comparison map. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

abbrev RecoveredPair (b n : ℕ) := ShiftedPair b × PrefixDatum n × PrefixDatum n

lemma recovered_pair_fiber_bound {b n D : ℕ}
    (Q : Finset (RecoveredPair b n)) (t : ShiftedPair b)
    (hD : 0 < D) (ht : 0 < t.remainder)
    (hp : ∀ q ∈ Q, (∀ i, 1 ≤ q.2.1.primes i) ∧ (∀ i, 1 ≤ q.2.2.primes i))
    (hprod : ∀ q ∈ Q,
      q.2.1.d * (∏ i, (q.2.1.primes i-1)) = D ∧
      q.2.2.d * (∏ i, (q.2.2.primes i-1)) = q.1.remainder) :
    (Q.filter (fun q => q.1 = t)).card ≤
      (n+1)^(D.primeFactorsList.length+t.remainder.primeFactorsList.length) := by
  classical
  let F := Q.filter (fun q => q.1 = t)
  let A := F.image (fun q => q.2.1)
  let B := F.image (fun q => q.2.2)
  have ha : A.card ≤ (n+1)^D.primeFactorsList.length := by
    apply prefixData_card_le hD A
    · intro a ha i
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp ha
      exact (hp q (Finset.mem_filter.mp hq).1).1 i
    · intro a ha
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp ha
      exact (hprod q (Finset.mem_filter.mp hq).1).1
  have hb : B.card ≤ (n+1)^t.remainder.primeFactorsList.length := by
    apply prefixData_card_le ht B
    · intro a ha i
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp ha
      exact (hp q (Finset.mem_filter.mp hq).1).2 i
    · intro a ha
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp ha
      rw [← (Finset.mem_filter.mp hq).2]
      exact (hprod q (Finset.mem_filter.mp hq).1).2
  have hinj : F.card ≤ (A ×ˢ B).card := by
    apply Finset.card_le_card_of_injOn (fun q : RecoveredPair b n => q.2)
    · intro q hq
      exact Finset.mem_product.mpr
        ⟨Finset.mem_image.mpr ⟨q, hq, rfl⟩, Finset.mem_image.mpr ⟨q, hq, rfl⟩⟩
    · intro q hq q' hq' he
      apply Prod.ext
      · exact (Finset.mem_filter.mp hq).2.trans (Finset.mem_filter.mp hq').2.symm
      · exact he
  calc
    _ ≤ (A ×ˢ B).card := hinj
    _ = A.card*B.card := Finset.card_product _ _
    _ ≤ (n+1)^D.primeFactorsList.length * (n+1)^t.remainder.primeFactorsList.length :=
      Nat.mul_le_mul ha hb
    _ = _ := (pow_add _ _ _).symm

/-- Ford's comparison counts prime lists and one residual integer. Restoring
both missing prefix tails costs only their prime-occurrence allocations. -/
theorem ford_comparison_with_recovery (hford : FordLemma51Input) :
    ∃ C y₀ : ℝ, 0 < C ∧ 1 < y₀ ∧
    ∀ (b n K : ℕ) (y S : ℝ) (D r : ℕ) (Y U : ℕ → ℝ),
      y₀ ≤ y → FordComparisonParameters b y S D r Y U →
      ∀ Q : Finset (RecoveredPair b n),
        (∀ q ∈ Q, FordComparisonConditions b y S D r Y U q.1) →
        (∀ q ∈ Q, q.1.remainder.primeFactorsList.length ≤ K) →
        (∀ q ∈ Q, (∀ i, 1 ≤ q.2.1.primes i) ∧ (∀ i, 1 ≤ q.2.2.primes i)) →
        (∀ q ∈ Q, q.2.1.d * (∏ i, (q.2.1.primes i-1)) = D ∧
          q.2.2.d * (∏ i, (q.2.2.primes i-1)) = q.1.remainder) →
        (Q.card : ℝ) ≤ (n+1 : ℝ)^(D.primeFactorsList.length+K) *
          fordComparisonBound C b y S D r Y U := by
  classical
  obtain ⟨C, y₀, hC, hy₀, hford⟩ := hford
  refine ⟨C, y₀, hC, hy₀, ?_⟩
  intro b n K y S D r Y U hy hparam Q hcond hK hp hprod
  let T := Q.image Prod.fst
  have hT : ∀ t ∈ T, FordComparisonConditions b y S D r Y U t := by
    intro t ht
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp ht
    exact hcond q hq
  have hD : 0 < D := hparam.2.2.2.2.2.2.2.1
  have hcard : Q.card ≤ T.card*(n+1)^(D.primeFactorsList.length+K) := by
    rw [Finset.card_eq_sum_card_image Prod.fst Q]
    calc
      _ ≤ ∑ _t ∈ T, (n+1)^(D.primeFactorsList.length+K) := by
        apply Finset.sum_le_sum
        intro t ht
        obtain ⟨q, hq, hqt⟩ := Finset.mem_image.mp ht
        have hr := (hcond q hq).1
        have hk := hK q hq
        rw [hqt] at hr hk
        exact (recovered_pair_fiber_bound Q t hD hr hp hprod).trans
          (Nat.pow_le_pow_right (by omega) (Nat.add_le_add_left hk _))
      _ = _ := by simp [T, Nat.mul_comm]
  have hbound := hford b y S D r Y U hy hparam T hT
  have hreal : (Q.card : ℝ) ≤ (T.card : ℝ)*(n+1 : ℝ)^(D.primeFactorsList.length+K) := by
    exact_mod_cast hcard
  calc
    _ ≤ (T.card : ℝ)*(n+1 : ℝ)^(D.primeFactorsList.length+K) := hreal
    _ ≤ fordComparisonBound C b y S D r Y U * (n+1 : ℝ)^(D.primeFactorsList.length+K) :=
      mul_le_mul_of_nonneg_right hbound (by positivity)
    _ = _ := mul_comm _ _

end TotientAsymptotic

end

end OAI
