import OAI.NumberTheory.Ostmann.Arithmetic.HistorySupportDescentLists

namespace OAI

namespace Ostmann.Arithmetic.HistorySupportDescent

theorem prime_list_pairwise {u : List ℕ} (hnd : u.Nodup)
    (hp : ∀ b ∈ u, Nat.Prime b) : u.Pairwise Nat.Coprime := by
  apply hnd.pairwise_of_forall_ne
  intro a ha b hb hab
  exact (Nat.coprime_primes (hp a ha) (hp b hb)).mpr hab

theorem prod_dvd_iff {u : List ℕ} (hu : u.Pairwise Nat.Coprime) (N : ℤ) :
    (u.prod : ℤ) ∣ N ↔ ∀ b ∈ u, (b : ℤ) ∣ N := by
  constructor
  · intro h b hb
    apply dvd_trans _ h
    exact_mod_cast List.dvd_prod hb
  · intro h
    induction u with
    | nil => simp
    | cons b u ih =>
      obtain ⟨hbu,hu⟩ := List.pairwise_cons.mp hu
      have hc : IsCoprime (b : ℤ) (u.prod : ℤ) :=
        (Nat.coprime_list_prod_right_iff.mpr hbu).isCoprime
      simpa only [List.prod_cons,Nat.cast_mul] using
        hc.mul_dvd (h b (by simp)) (ih hu (fun a ha => h a (by simp [ha])))

theorem frequency_prod_coprime (s : ℤ) (u : List ℕ)
    (hs : ∀ b ∈ u, IsCoprime s (b : ℤ)) : IsCoprime s (u.prod : ℤ) := by
  induction u with
  | nil => exact isCoprime_one_right
  | cons b u ih =>
    simp only [List.prod_cons,Nat.cast_mul,IsCoprime.mul_right_iff]
    exact ⟨hs b (by simp),ih (fun a ha => hs a (by simp [ha]))⟩

theorem integrality_iff {u : List ℕ} {s N : ℤ}
    (hu : u.Pairwise Nat.Coprime) (hs : ∀ b ∈ u, IsCoprime s (b : ℤ)) :
    (∃ p : ℤ, N = s * (u.prod : ℤ) * p) ↔
      s ∣ N ∧ ∀ b ∈ u, (b : ℤ) ∣ N := by
  rw [integral_reversal_iff (frequency_prod_coprime s u hs),prod_dvd_iff hu N]

theorem prime_integrality_iff {u : List ℕ} {s N : ℤ}
    (hnd : u.Nodup) (hp : ∀ b ∈ u, Nat.Prime b)
    (hs : ∀ b ∈ u, IsCoprime s (b : ℤ)) :
    (∃ p : ℤ, N = s * (u.prod : ℤ) * p) ↔
      s ∣ N ∧ ∀ b ∈ u, (b : ℤ) ∣ N :=
  integrality_iff (prime_list_pairwise hnd hp) hs

end Ostmann.Arithmetic.HistorySupportDescent

end OAI
