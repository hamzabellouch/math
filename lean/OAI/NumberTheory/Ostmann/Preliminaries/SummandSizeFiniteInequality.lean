import OAI.NumberTheory.Ostmann.Supply.NaturalPrimeSupportSieve
import OAI.NumberTheory.Ostmann.Preliminaries.ReciprocalSupportCauchy

namespace OAI

/-! # The finite sieve/collision inequality underlying the square-root bounds

The prime set and the second sampling length are independent. This retains the
freedom to choose a very long second prefix in the subpower bootstrap.
-/

namespace Ostmann

open scoped Classical BigOperators

 theorem EventuallyPrimeSumset.summand_size_finite_inequality {A B : Set ℕ}
    (h : EventuallyPrimeSumset A B) (hB : B.Nonempty) :
    ∃ N₀ : ℕ, ∀ X Q Y : ℕ, ∀ P : Finset ℕ, ∀ ell : ℝ,
      1 ≤ Q → 1 ≤ Y → 0 ≤ ell →
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, p ≤ Q) →
      (∀ p ∈ P, ell ≤ Real.log (p : ℝ)) →
      (summandTail A (N₀ + Q) X).Nonempty → (summandPrefix B Y).Nonempty →
      ((summandTail A (N₀ + Q) X).card : ℝ) * (ell * (P.card : ℝ) ^ 2) ≤
        (Q : ℝ) * (((X + 1 : ℕ) : ℝ) + (Q : ℝ) ^ 2) *
          (Real.log (Y : ℝ) + (1 / ((summandPrefix B Y).card : ℝ)) *
            ∑ p ∈ P, Real.log (p : ℝ)) := by
  obtain ⟨N₀, hN⟩ := h.tail_full_support_prime_sieve
  refine ⟨N₀, ?_⟩
  intro X Q Y P ell hQ hY hell hP hPQ hlog hU hV
  let m : ℝ := (summandTail A (N₀ + Q) X).card
  let R : ℝ := ((X + 1 : ℕ) : ℝ) + (Q : ℝ) ^ 2
  let H : ℝ := ∑ p ∈ P, Real.log (p : ℝ) / ((occupiedResidues B p).card : ℝ)
  have hm : 0 < m := by dsimp [m]; exact_mod_cast hU.card_pos
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hq : 0 ≤ (Q : ℝ) := Nat.cast_nonneg Q
  have hcs := occupied_support_cauchy B hB P hP (Q : ℝ) (R / m) ell hq
    (div_nonneg hR hm.le) hell (fun p hp => by exact_mod_cast hPQ p hp) hlog
    (hN X Q P hQ hP hPQ hU)
  have hcol := summandPrefix_occupied_bound B P Y hY hV hP
  have hmcs := mul_le_mul_of_nonneg_left hcs hm.le
  have heq : m * ((Q : ℝ) * (R / m) * H) = (Q : ℝ) * R * H := by
    field_simp
  change m * (ell * (P.card : ℝ) ^ 2) ≤ _
  change m * (ell * (P.card : ℝ) ^ 2) ≤ m * ((Q : ℝ) * (R / m) * H) at hmcs
  rw [heq] at hmcs
  exact hmcs.trans (mul_le_mul_of_nonneg_left hcol (mul_nonneg hq hR))

end Ostmann

end OAI
