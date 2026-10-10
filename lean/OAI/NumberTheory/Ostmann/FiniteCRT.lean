import OAI.NumberTheory.Ostmann.Statement

namespace OAI

namespace Ostmann

theorem shifted_difference_coprime {q a b : ℕ} (hq : q.Prime)
    (ha : a < q) (hb : b < q) (hab : a ≠ b) : (q + a - b).Coprime q := by
  apply Nat.Coprime.symm
  apply hq.coprime_iff_not_dvd.mpr
  intro hd
  have he : q + a - b + b = q + a := Nat.sub_add_cancel (by omega)
  have hm := (Nat.modEq_zero_iff_dvd.mpr hd).add_right b
  rw [he] at hm
  simp only [Nat.ModEq, Nat.add_mod_left, Nat.zero_add,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hm
  exact hab hm

noncomputable def separatingPrime (M a : ℕ) : ℕ := Nat.nth Nat.Prime (M + a)

theorem separatingPrime_prime (M a : ℕ) : (separatingPrime M a).Prime :=
  Nat.prime_nth_prime (M+a)

theorem lt_separatingPrime (M a : ℕ) : M < separatingPrime M a := by
  have h := Nat.add_two_le_nth_prime (M+a)
  dsimp [separatingPrime]
  omega

theorem separatingPrime_injective (M : ℕ) : Function.Injective (separatingPrime M) := by
  intro a b h
  have hab := (Nat.nth_strictMono Nat.infinite_setOfPred_prime).injective h
  exact Nat.add_left_cancel hab

theorem exists_reduced_class (t : Finset ℕ) (f : ℕ → ℕ) (M : ℕ)
    (ha : ∀ a ∈ t, a ≤ M) (hf : ∀ a ∈ t, f a ≤ M)
    (hne : ∀ a ∈ t, a ≠ f a) :
    ∃ Q r : ℕ, Q ≠ 0 ∧ r.Coprime Q ∧
      ∀ a ∈ t, r ≡ separatingPrime M a + a - f a [MOD separatingPrime M a] ∧
        separatingPrime M a ∣ Q := by
  classical
  let q := separatingPrime M
  let c := fun a => q a + a - f a
  have hq : ∀ a, (q a).Prime := separatingPrime_prime M
  have hnonzero : ∀ a ∈ t, q a ≠ 0 := fun a _ => (hq a).ne_zero
  have hpair : Set.Pairwise (↑t : Set ℕ) (fun a b => (q a).Coprime (q b)) := by
    intro a _ b _ hab
    exact (Nat.coprime_primes (hq a) (hq b)).mpr
      (fun h => hab (separatingPrime_injective M h))
  let r := Nat.chineseRemainderOfFinset c q t hnonzero hpair
  have hr : ∀ a ∈ t, (r : ℕ) ≡ c a [MOD q a] := r.property
  have hc : ∀ a ∈ t, (c a).Coprime (q a) := by
    intro a hat
    exact shifted_difference_coprime (hq a)
      ((ha a hat).trans_lt (lt_separatingPrime M a))
      ((hf a hat).trans_lt (lt_separatingPrime M a)) (hne a hat)
  refine ⟨∏ a ∈ t, q a, r, Finset.prod_ne_zero_iff.mpr hnonzero, ?_, ?_⟩
  · apply Nat.coprime_prod_right_iff.mpr
    intro a hat
    have hmod := hr a hat
    change (r : ℕ) % q a = c a % q a at hmod
    rw [← ZMod.coprime_mod_iff_coprime, hmod, ZMod.coprime_mod_iff_coprime]
    exact hc a hat
  · intro a hat
    exact ⟨hr a hat, Finset.dvd_prod_of_mem q hat⟩

end Ostmann

end OAI
