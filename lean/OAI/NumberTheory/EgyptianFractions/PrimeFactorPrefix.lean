import Mathlib

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337

/-- A finite product crosses any threshold lying between its initial multiplier
and its final value. No monotonicity assumptions on the factors are needed. -/
theorem list_product_crossing (l : List ℕ) (d : ℕ) (y : ℝ)
    (hdy : (d : ℝ) ≤ y) (hy : y < (d * l.prod : ℕ)) :
    ∃ a : List ℕ, ∃ p : ℕ, ∃ b : List ℕ,
      l = a ++ p :: b ∧ (d * a.prod : ℕ) ≤ y ∧ y < (d * a.prod * p : ℕ) := by
  induction l generalizing d with
  | nil => simp only [List.prod_nil, mul_one] at hy; linarith
  | cons p l ih =>
    by_cases hp : y < (d * p : ℕ)
    · exact ⟨[], p, l, rfl, by simpa using hdy, by simpa using hp⟩
    · have hdp : (d * p : ℕ) ≤ y := le_of_not_gt hp
      have htail : y < ((d * p) * l.prod : ℕ) := by
        simpa only [List.prod_cons, Nat.mul_assoc] using hy
      obtain ⟨a, q, b, hl, ha, hq⟩ := ih (d * p) hdp htail
      refine ⟨p :: a, q, b, by simp [hl], ?_, ?_⟩
      · simpa only [List.prod_cons, Nat.mul_assoc] using ha
      · simpa only [List.prod_cons, Nat.mul_assoc] using hq

/-- The longest sorted prime-factor prefix below a real threshold.
The two prime-factor separation statements allow the smooth and rough parts
of the divisor-moment argument to be estimated independently. -/
theorem prime_factor_prefix (n : ℕ) (y : ℝ) (hy : 1 ≤ y) (hyn : y < n) :
    ∃ d p : ℕ, 0 < d ∧ p.Prime ∧ d ∣ n ∧
      (d : ℝ) ≤ y ∧ y < (d * p : ℕ) ∧ p ∣ n / d ∧
      (∀ q : ℕ, q.Prime → q ∣ d → q ≤ p) ∧
      (∀ q : ℕ, q.Prime → q ∣ n / d → p ≤ q) := by
  have hnpos : 0 < n := by exact_mod_cast (show (0 : ℝ) < n by linarith)
  have hprod := Nat.prod_primeFactorsList hnpos.ne'
  obtain ⟨a, p, b, hsplit, ha, hp⟩ := list_product_crossing n.primeFactorsList 1 y
    (by simpa using hy) (by simpa [hprod] using hyn)
  simp only [one_mul] at ha hp
  have hprimes : ∀ q ∈ a ++ p :: b, q.Prime := by
    intro q hq
    exact Nat.prime_of_mem_primeFactorsList (hsplit ▸ hq)
  have hpa : ∀ q ∈ a, q.Prime := fun q hq => hprimes q (List.mem_append_left _ hq)
  have hpb : ∀ q ∈ p :: b, q.Prime := fun q hq => hprimes q (List.mem_append_right _ hq)
  have hd : 0 < a.prod := List.prod_pos (fun q hq => (hpa q hq).pos)
  have he : 0 < (p :: b).prod := List.prod_pos (fun q hq => (hpb q hq).pos)
  have hmul : n = a.prod * (p :: b).prod := by
    rw [← hprod, hsplit, List.prod_append]
  have hdiv : n / a.prod = (p :: b).prod := by
    rw [hmul, Nat.mul_div_cancel_left _ hd]
  have hsort := (Nat.primeFactorsList_sorted n).pairwise
  rw [hsplit] at hsort
  obtain ⟨hasort, hbsort, hcross⟩ := List.pairwise_append.mp hsort
  refine ⟨a.prod, p, hd, hpb p (by simp), ⟨(p :: b).prod, hmul⟩,
    ha, hp, ?_, ?_, ?_⟩
  · rw [hdiv]
    exact List.dvd_prod (by simp)
  · intro q hq hqd
    have hqmem : q ∈ a := (Nat.primeFactorsList_unique rfl hpa).mem_iff.mpr
      ((Nat.mem_primeFactorsList hd.ne').mpr ⟨hq, hqd⟩)
    exact hcross q hqmem p (by simp)
  · intro q hq hqd
    rw [hdiv] at hqd
    have hqmem : q ∈ p :: b := (Nat.primeFactorsList_unique rfl hpb).mem_iff.mpr
      ((Nat.mem_primeFactorsList he.ne').mpr ⟨hq, hqd⟩)
    rcases List.mem_cons.mp hqmem with heq | hqb
    · omega
    · exact (List.pairwise_cons.mp hbsort).1 q hqb

end Problem337

end

end OAI
