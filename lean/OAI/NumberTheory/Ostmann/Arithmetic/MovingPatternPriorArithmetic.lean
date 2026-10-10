import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternGiantSupport
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternBulkBudgets

namespace OAI

/-! # Arithmetic support under the unchanged representative prior -/

namespace Ostmann
open scoped Classical BigOperators

/-- The literal list of frequencies still lies in the finite source set. -/
theorem allFrequencyList_subtype_mem (S : Finset ℤ) (n : ℕ)
    (t : FrequencyTree S n) (s : ℤ)
    (hs : s ∈ allFrequencyList n (frequencyTreeMap Subtype.val n t)) : s ∈ S := by
  induction n with
  | zero =>
    have heq : s = Subtype.val t := by simpa only [frequencyTreeMap, allFrequencyList, List.mem_singleton] using hs
    simpa only [heq] using (Subtype.property t)
  | succ n ih =>
    simp only [frequencyTreeMap, allFrequencyList, List.mem_cons, List.mem_append] at hs
    rcases hs with heq | hs | hs
    · simpa only [heq] using (Subtype.property t.1)
    · exact ih t.2.1 hs
    · exact ih t.2.2 hs

/-- Range separation supplies the arithmetic support used when averaging
internal primes. The conclusion holds on the actual product prior, before
restricting to a nonzero observable. -/
theorem movingPattern_prior_arithmetic_support {A B C I : Type*} {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (μ : ℕ → A → ℝ) (ν : B → A → ℝ)
    (prime : A → ℕ) (hinj : Function.Injective prime) (hprime : ∀ a, (prime a).Prime)
    (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c})
    (tier : A → ℕ) (tierB : B → ℕ) (tierC : C → ℕ)
    (hμtier : ∀ j, j < n → ∀ a, μ j a ≠ 0 → tier a = j)
    (hνtier : ∀ j a, ν j a ≠ 0 → tier a = tierB j) (hB : ∀ b, n ≤ tierB b)
    (htierC : ∀ i, tierC (pattern i) = movingSampleTier i.2)
    (S : Finset ℤ) (V lo : ℕ) (ft : FrequencyTree (S × S) n)
    (hS : ∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ V) (hVlo : V ≤ lo)
    (hμlo : ∀ j a, μ j a ≠ 0 → lo < prime a)
    (hνlo : ∀ j a, ν j a ≠ 0 → lo < prime a)
    (p : I → ℕ) (hp : ∀ i, (p i).Prime) (hplo : ∀ i, p i ≤ lo)
    (t : Bool → FrequencyTree ℤ n)
    (small : Bool → TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
    (hf : ∀ b, ∀ s ∈ allFrequencyList n (t b), s ≠ 0)
    (hfreq : ∀ b, ∀ s ∈ allFrequencyList n (t b), s.natAbs ≤ V)
    (x : Fin (N + 1) → A)
    (hx : productPrior (fun i => Sum.elim ν
      (fun c => μ (movingSampleTier (rep c).val.2)) (e i)) x ≠ 0) :
    (∀ i, IsCoprime (prime (x i) : ℤ) (frequencyModelBase S n ft : ℤ)) ∧
    (∀ i j, (prime (x j) : ZMod (p i)) ≠ 0) ∧
    (∀ i j, (Sum.elim tierB tierC) (e i) ≠ (Sum.elim tierB tierC) (e j) →
      prime (x i) ≠ prime (x j)) ∧
    (∀ b c, prime (x (e.symm (.inl b))) ≠ prime (x (e.symm (.inr c)))) ∧
    (∀ c b, (movingPatternFinBulkData e n m t small slot perm pattern b).Frequencies
      (fun s => (s : ZMod (prime (x (e.symm (.inr c))))) ≠ 0)) := by
  have hlarge := movingPattern_prior_lower e μ ν prime pattern rep lo hμlo hνlo x hx
  have hlargeV (i) : V < prime (x i) := hVlo.trans_lt (hlarge i)
  have hcop := movingPattern_prior_frequency_coprime e μ ν prime hprime pattern rep S V ft hS
    (fun j a ha => hVlo.trans_lt (hμlo j a ha))
    (fun j a ha => hVlo.trans_lt (hνlo j a ha)) x hx
  have hsep := movingPattern_prior_prime_separation e μ ν pattern rep tier tierB prime hinj
    hμtier hνtier hB x hx
  have htierEq : tierC = fun c => movingSampleTier (rep c).val.2 := by
    funext c
    have h := htierC (rep c).val
    simpa only [(rep c).property] using h
  refine ⟨?_, ?_, ?_, hsep.2, ?_⟩
  · intro i
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_def, Int.natAbs_natCast, Int.natAbs_natCast]
    exact hcop i
  · intro i j hz
    have hd := (ZMod.natCast_eq_zero_iff (prime (x j)) (p i)).mp hz
    have heq := (Nat.prime_dvd_prime_iff_eq (hp i) (hprime _)).mp hd
    have hlt := (hplo i).trans_lt (hlarge j)
    omega
  · simpa only [htierEq] using hsep.1
  · intro c b
    let T := movingPatternFinBulkData e n m t small slot perm pattern b
    exact T.small_frequency_residues (fun i => prime (x i)) (fun i => hprime _)
      V hlargeV (movingPatternFinBulkData_frequencies e t small slot perm pattern _ hf b)
      (movingPatternFinBulkData_frequencies e t small slot perm pattern _ hfreq b) (e.symm (.inr c))

end Ostmann

end OAI
