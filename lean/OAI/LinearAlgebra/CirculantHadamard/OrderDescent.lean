import OAI.LinearAlgebra.CirculantHadamard.OrderHalving
import OAI.LinearAlgebra.CirculantHadamard.ModEight

namespace OAI

/-!
# Finite descent of an odd dyadic cyclic norm

The invariant `1 ≤ t` and `t + 2 ≤ k` records exactly the range needed to
halve an odd row until its norm is `4*u^2` while retaining a group order
divisible by eight. Every step invokes the concrete cyclotomic halving
theorem. The final step is the coefficient-square contradiction modulo eight.
-/

noncomputable section

namespace CirculantHadamard

open CyclicRing

/-- An odd-coefficient dyadic cyclic norm cannot have two more group
exponents than norm half-exponents. No halving is performed when `t = 1`. -/
theorem odd_norm_impossible {k t u : ℕ}
    (ht : 1 ≤ t) (hkt : t + 2 ≤ k) (hu : Odd u)
    (T : Elem ℤ (2 ^ k)) (hodd : ∀ a, Odd (T.coeff a))
    (hnorm : T * ringStar T = scalar (2 ^ k) ((2 ^ (2 * t) * u ^ 2 : ℕ) : ℤ)) :
    False := by
  suffices main : ∀ t k : ℕ, 1 ≤ t → t + 2 ≤ k →
      ∀ T : Elem ℤ (2 ^ k), (∀ a, Odd (T.coeff a)) →
        T * ringStar T = scalar (2 ^ k) ((2 ^ (2 * t) * u ^ 2 : ℕ) : ℤ) →
          False by
    exact main t k ht hkt T hodd hnorm
  intro t
  induction t with
  | zero =>
      intro k ht
      omega
  | succ t ih =>
      intro k ht hkt T hodd hnorm
      cases t with
      | zero =>
          have hcard : 8 ∣ 2 ^ k := by
            have hpow : (2 : ℕ) ^ 3 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
            norm_num at hpow
            exact hpow
          apply odd_norm_four_impossible hcard hu T hodd
          simpa only [Nat.zero_add, Nat.mul_one, Nat.reducePow] using hnorm
      | succ t =>
          cases k with
          | zero => omega
          | succ k =>
              obtain ⟨U, hUodd, hUnorm⟩ := exists_odd_halving
                k (t + 1 + 1) u T (by omega) hu hodd hnorm
              apply ih k (by omega) (by omega) U hUodd
              simpa only [Nat.add_sub_cancel] using hUnorm

theorem initial_even_power_norm_impossible {s u : ℕ} (hs : 2 ≤ s) (hu : Odd u)
    (T : Elem ℤ (2 ^ (2 * s))) (hodd : ∀ a, Odd (T.coeff a))
    (hnorm : T * ringStar T =
      scalar (2 ^ (2 * s)) ((2 ^ (2 * s) * u ^ 2 : ℕ) : ℤ)) : False :=
  odd_norm_impossible (by omega) (by omega) hu T hodd hnorm

end CirculantHadamard

end

end OAI
