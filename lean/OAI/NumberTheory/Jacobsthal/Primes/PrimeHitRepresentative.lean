import OAI.NumberTheory.Jacobsthal.Estimates.PositiveProgression

namespace OAI

namespace Erdos970

section

namespace ErdosInverseHits

theorem modEq_prime_product_iff (P : Finset ℕ) (hP : ∀ p ∈ P,p.Prime) (n b : ℕ) :
    Nat.ModEq (∏ p ∈ P,p) n b ↔ ∀ p ∈ P,Nat.ModEq p n b := by
  classical
  revert hP
  induction P using Finset.induction_on with
  | empty => intro _;simp [Nat.modEq_one]
  | @insert p P hp ih =>
    intro hP
    have hprime := hP p (Finset.mem_insert_self _ _)
    have hrest : ∀ q ∈ P,q.Prime := fun q hq => hP q (Finset.mem_insert_of_mem hq)
    have hco : p.Coprime (∏ q ∈ P,q) := by
      apply Nat.Coprime.prod_right
      intro q hq
      exact (Nat.coprime_primes hprime (hrest q hq)).mpr (by intro heq;exact hp (heq ▸ hq))
    rw [Finset.prod_insert hp,← Nat.modEq_and_modEq_iff_modEq_mul hco,ih hrest]
    simp only [Finset.forall_mem_insert]

theorem exists_prime_hit_representative (q : ℕ) (hq : Squarefree q) (a : ℕ → ℕ) :
    ∃ b : ℕ,1 ≤ b ∧ b ≤ q ∧ ∀ n : ℕ,
      (∀ p ∈ q.primeFactors,n%p = a p%p) ↔ Nat.ModEq q n b := by
  classical
  have hq0 : 0 < q := Nat.pos_of_ne_zero hq.ne_zero
  have hnz : ∀ p ∈ q.primeFactors,(id p : ℕ) ≠ 0 :=
    fun p hp => (Nat.prime_of_mem_primeFactors hp).ne_zero
  have hpair : Set.Pairwise (q.primeFactors : Set ℕ) (fun p r => Nat.Coprime (id p) (id r)) := by
    intro p hp r hr hpr
    exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
      (Nat.prime_of_mem_primeFactors hr)).mpr hpr
  let c := Nat.chineseRemainderOfFinset a id q.primeFactors hnz hpair
  have hcq : c.val < q := by
    have hh := Nat.chineseRemainderOfFinset_lt_prod a id hnz hpair
    simpa only [id_eq,Nat.prod_primeFactors_of_squarefree hq] using hh
  have hbp : ∃ b : ℕ,1 ≤ b ∧ b ≤ q ∧ ∀ p ∈ q.primeFactors,Nat.ModEq p b (a p) := by
    by_cases hc : c.val = 0
    · refine ⟨q,hq0,le_rfl,?_⟩
      intro p hp
      have hd : p ∣ q := Nat.dvd_of_mem_primeFactors hp
      have ht := c.property p hp
      change Nat.ModEq p c.val (a p) at ht
      rw [hc] at ht
      exact hd.modEq_zero_nat.trans ht
    · exact ⟨c.val,by omega,hcq.le,c.property⟩
  obtain ⟨b,hb1,hbq,hbp⟩ := hbp
  refine ⟨b,hb1,hbq,?_⟩
  intro n
  have hprod := modEq_prime_product_iff q.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp) n b
  rw [Nat.prod_primeFactors_of_squarefree hq] at hprod
  rw [hprod]
  constructor
  · intro hn p hp
    exact (show Nat.ModEq p n (a p) from hn p hp).trans (hbp p hp).symm
  · intro hn p hp
    exact (hn p hp).trans (hbp p hp)

noncomputable def primeHitRepresentative (q : ℕ) (hq : Squarefree q) (a : ℕ → ℕ) : ℕ :=
  (exists_prime_hit_representative q hq a).choose

theorem primeHitRepresentative_spec (q : ℕ) (hq : Squarefree q) (a : ℕ → ℕ) :
    1 ≤ primeHitRepresentative q hq a ∧ primeHitRepresentative q hq a ≤ q ∧
      ∀ n : ℕ,(∀ p ∈ q.primeFactors,n%p = a p%p) ↔ Nat.ModEq q n (primeHitRepresentative q hq a) :=
  (exists_prime_hit_representative q hq a).choose_spec

end ErdosInverseHits

end

end Erdos970

end OAI
