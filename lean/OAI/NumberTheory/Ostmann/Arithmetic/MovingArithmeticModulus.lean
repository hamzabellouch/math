import OAI.NumberTheory.Ostmann.Arithmetic.MovingArithmeticBlocks

namespace OAI

/-! # Coprimality of the concrete arithmetic blocks -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingArithmeticModuli_ne_zero {I : Type*} (r : ℕ) (q : I → ℕ)
    (P : Finset ℕ) (S : Finset I) (hr : r ≠ 0)
    (hp : ∀ p ∈ P, p.Prime) (hq : ∀ i ∈ S, (q i).Prime)
    (b : MovingArithmeticBlocks P S) : movingArithmeticModuli r q P S b ≠ 0 := by
  rcases b with u | (p | i)
  · exact hr
  · exact pow_ne_zero _ (hp p.val p.property).ne_zero
  · exact (hq i.val i.property).ne_zero

theorem movingArithmeticModuli_coprime {I : Type*} (r : ℕ) (q : I → ℕ)
    (P : Finset ℕ) (S : Finset I)
    (hp : ∀ p ∈ P, p.Prime) (hq : ∀ i ∈ S, (q i).Prime)
    (hinj : Set.InjOn q S)
    (hrp : ∀ p ∈ P, r.Coprime p) (hrq : ∀ i ∈ S, r.Coprime (q i))
    (hd : ∀ p ∈ P, ∀ i ∈ S, p ≠ q i) :
    Pairwise (fun b c => (movingArithmeticModuli r q P S b).Coprime
      (movingArithmeticModuli r q P S c)) := by
  rintro (u | (p | i)) (v | (t | j)) hne
  · cases u; cases v
    exact False.elim (hne rfl)
  · exact (hrp t.val t.property).pow_right 2
  · exact hrq j.val j.property
  · exact (hrp p.val p.property).symm.pow_left 2
  · have hpt : p.val ≠ t.val := fun h => hne (by rw [Subtype.ext h])
    exact (((Nat.coprime_primes (hp p.val p.property) (hp t.val t.property)).mpr hpt).pow_left 2).pow_right 2
  · exact ((Nat.coprime_primes (hp p.val p.property) (hq j.val j.property)).mpr
      (hd p.val p.property j.val j.property)).pow_left 2
  · exact (hrq i.val i.property).symm
  · exact ((Nat.coprime_primes (hp t.val t.property) (hq i.val i.property)).mpr
      (hd t.val t.property i.val i.property)).symm.pow_right 2
  · have hij : q i.val ≠ q j.val := fun h =>
      hne (by rw [Subtype.ext (hinj i.property j.property h)])
    exact (Nat.coprime_primes (hq i.val i.property) (hq j.val j.property)).mpr hij

/-- The three arithmetic periods divide the concrete CRT modulus. -/
theorem movingArithmeticModuli_periods {I : Type*} (r : ℕ) (q : I → ℕ)
    (P : Finset ℕ) (S : Finset I) (R : ℤ) (k : ℕ) (hR : R ^ k ∣ (r : ℤ)) :
    (R ^ k ∣ ((∏ b, movingArithmeticModuli r q P S b : ℕ) : ℤ)) ∧
    (∀ p ∈ P, (p ^ 2 : ℤ) ∣ ((∏ b, movingArithmeticModuli r q P S b : ℕ) : ℤ)) ∧
    (∀ i ∈ S, (q i : ℤ) ∣ ((∏ b, movingArithmeticModuli r q P S b : ℕ) : ℤ)) := by
  constructor
  · apply hR.trans
    exact_mod_cast (Finset.dvd_prod_of_mem (movingArithmeticModuli r q P S)
      (Finset.mem_univ (Sum.inl ())))
  constructor
  · intro p hp
    have h : p ^ 2 ∣ ∏ b, movingArithmeticModuli r q P S b :=
      Finset.dvd_prod_of_mem (movingArithmeticModuli r q P S)
        (Finset.mem_univ (Sum.inr (Sum.inl (⟨p, hp⟩ : P))))
    exact_mod_cast h
  · intro i hi
    have h : q i ∣ ∏ b, movingArithmeticModuli r q P S b :=
      Finset.dvd_prod_of_mem (movingArithmeticModuli r q P S)
        (Finset.mem_univ (Sum.inr (Sum.inr (⟨i, hi⟩ : S))))
    exact_mod_cast h

end Ostmann

end OAI
