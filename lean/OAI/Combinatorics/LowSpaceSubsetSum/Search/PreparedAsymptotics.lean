import OAI.Combinatorics.LowSpaceSubsetSum.Search.PreparedDecisionWordBounds

namespace OAI

/-! # Polynomial-bit resource envelopes for the prepared decision procedure -/

noncomputable section
namespace LowSpaceSubsetSum.PreparedAsymptotics

open Filter

theorem capacity_upper (n : ℕ) : (compressionDictionaryCapacity n : ℝ) ≤
    (2 : ℝ)^((199/1000 : ℝ)*n) := by
  have h : 1000*(199*n/1000) ≤ 199*n := Nat.mul_div_le _ _
  have hr : (1000 : ℝ)*(199*n/1000 : ℕ) ≤ 199*n := by exact_mod_cast h
  have he : ((199*n/1000 : ℕ) : ℝ) ≤ (199/1000 : ℝ)*n := by linarith only [hr]
  simpa only [compressionDictionaryCapacity, Nat.cast_pow, Nat.cast_ofNat,
    Real.rpow_natCast] using
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) he

theorem space (c : ℕ) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, ∀ I : Instance n, inputBits I ≤ n^c →
      (writableWordLimit I : ℝ) ≤ (3 : ℝ)^15*(2 : ℝ)^((1/5 : ℝ)*n) := by
  filter_upwards [one_fifth_space_polynomial c hc] with n hn
  intro I hI
  apply le_trans _ (hn (inputBits I) hI)
  simp only [writableWordLimit, Nat.cast_mul, Nat.cast_pow]
  exact mul_le_mul_of_nonneg_left (capacity_upper n) (by positivity)

theorem time (c : ℕ) (hc : 0 < c) (n : ℕ) (hn : 2 ≤ n)
    (I : Instance n) (hI : inputBits I ≤ n^c) :
    ((inputScale I^622*2^((n+1)/2) : ℕ) : ℝ) ≤
      ((3 : ℝ)^622*2)*(n : ℝ)^(622*c)*(2 : ℝ)^((1/2 : ℝ)*n) := by
  have hu : (inputScale I : ℝ) ≤ 3*(n : ℝ)^c := by
    exact_mod_cast polynomial_bit_bound hn hc hI
  have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ inputScale I) hu 622
  have hhalf : (((n+1)/2 : ℕ) : ℝ) ≤ (1/2 : ℝ)*n+1 := by
    have h : 2*((n+1)/2) ≤ n+1 := by omega
    have hh : (2 : ℝ)*((n+1)/2 : ℕ) ≤ n+1 := by exact_mod_cast h
    linarith only [hh]
  have he := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hhalf
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  apply (mul_le_mul hp (by simpa only [Real.rpow_natCast] using he)
    (by positivity) (by positivity)).trans
  rw [mul_pow, ← pow_mul, Nat.mul_comm c 622,
    Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
  exact le_of_eq (by ac_rfl)

end LowSpaceSubsetSum.PreparedAsymptotics

end

end OAI
