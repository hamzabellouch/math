import OAI.Combinatorics.EditApproximation.Geometry.BandEnvelopes
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-!
# Integer rounding spacings from the dyadic band envelopes

Taking the nonnegative part of the dyadic product exponent computes the
integer spacing max(1, theta*h). The resulting spacing preserves the wide
grid by actual divisibility of powers of two.
-/

namespace EditApproximation

open Finset





theorem dyadic_nonnegative_spacing (exponent : ℤ) :
    ((2 ^ exponent.toNat : ℕ) : ℚ) = max 1 ((2 : ℚ) ^ exponent) := by
  by_cases hnonneg : 0 ≤ exponent
  · have hcast : ((exponent.toNat : ℕ) : ℤ) = exponent := Int.toNat_of_nonneg hnonneg
    have hone : (1 : ℚ) ≤ 2 ^ exponent := by
      exact one_le_zpow₀ (by norm_num) hnonneg
    rw [max_eq_right hone, Nat.cast_pow, Nat.cast_ofNat, ← zpow_natCast, hcast]
  · have hnegative : exponent ≤ 0 := by omega
    have htoNat : exponent.toNat = 0 := Int.toNat_eq_zero.mpr hnegative
    have hone : (2 : ℚ) ^ exponent ≤ 1 := by
      simpa only [zpow_zero] using zpow_le_zpow_right₀ (by norm_num : (1 : ℚ) ≤ 2) hnegative
    simp only [htoNat, pow_zero, Nat.cast_one, max_eq_left hone]

theorem bandRoundSpacing_exact {ny M : ℕ} (thetaExponent b : ℕ)
    (band : List (Fin M → TargetInterval ny))
    (initial : Fin M → TargetInterval ny → ℚ) (i : Fin M) :
    (bandRoundSpacing thetaExponent b band initial i : ℚ) =
      max 1 ((2 : ℚ) ^ (-(thetaExponent : ℤ)) * bandChildEnvelope b band initial i) := by
  rw [bandRoundSpacing, dyadic_nonnegative_spacing]
  unfold bandChildEnvelope rationalDyadicCeiling bandEnvelopeExponent
  rw [← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
  congr 2
  omega

theorem bandRoundSpacing_pos {ny M : ℕ} (thetaExponent b : ℕ)
    (band : List (Fin M → TargetInterval ny))
    (initial : Fin M → TargetInterval ny → ℚ) (i : Fin M) :
    0 < bandRoundSpacing thetaExponent b band initial i := by
  unfold bandRoundSpacing
  positivity

/-- Actual division rounding moves each endpoint by at most the scaled
child envelope, including the special spacing-one case. -/
theorem gridRound_scaled_error (spacing position : ℕ) (scaled : ℚ)
    (hspacing : (spacing : ℚ) = max 1 scaled) (hscaled : 0 ≤ scaled) :
    (Nat.dist position (gridRound spacing position) : ℚ) ≤ scaled := by
  have hpos : 0 < spacing := by
    have hone : (1 : ℚ) ≤ spacing := by rw [hspacing]; exact le_max_left _ _
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℚ) < 1) hone)
  by_cases hone : spacing = 1
  · simp only [hone, gridRound_one, Nat.dist_self, Nat.cast_zero]
    exact hscaled
  · have htwo : 1 < spacing := by omega
    have htwoR : (1 : ℚ) < spacing := by exact_mod_cast htwo
    have hscale : 1 < scaled := by
      by_contra hnot
      have hle : scaled ≤ 1 := le_of_not_gt hnot
      rw [max_eq_left hle] at hspacing
      linarith only [hspacing, htwoR]
    have hequal : (spacing : ℚ) = scaled := hspacing.trans (max_eq_right hscale.le)
    have herr : (Nat.dist position (gridRound spacing position) : ℚ) < spacing := by
      exact_mod_cast gridRound_error_lt spacing position hpos
    exact herr.le.trans_eq hequal

theorem dyadic_dvd_of_le {small large : ℕ}
    (hsmall : ∃ e : ℕ, small = 2 ^ e) (hlarge : ∃ e : ℕ, large = 2 ^ e)
    (hle : small ≤ large) : small ∣ large := by
  obtain ⟨s, rfl⟩ := hsmall
  obtain ⟨l, rfl⟩ := hlarge
  exact Nat.pow_dvd_pow 2 ((Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hle)

theorem seedGridSpacing_dyadic {b P : ℕ}
    (hb : ∃ e : ℕ, b = 2 ^ e) (hP : ∃ e : ℕ, P = 2 ^ e) :
    ∃ e : ℕ, seedGridSpacing b P = 2 ^ e := by
  obtain ⟨s, rfl⟩ := hb
  obtain ⟨p, rfl⟩ := hP
  by_cases horder : p ≤ s
  · refine ⟨s - p, ?_⟩
    rw [seedGridSpacing, Nat.pow_div horder (by decide : 0 < 2), max_eq_right Nat.one_le_two_pow]
  · refine ⟨0, ?_⟩
    have hlt : 2 ^ s < 2 ^ p := Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega)
    simp only [seedGridSpacing, Nat.div_eq_of_lt hlt, max_eq_left (by decide : 0 ≤ 1), pow_zero]

/-- The envelope floor and the numerical theta*P ≥ M ensure that the
actual rounded integer spacing is a multiple of the actual wide grid. -/
theorem bandRoundSpacing_wide_grid {ny M b P : ℕ} (thetaExponent : ℕ)
    (band : List (Fin M → TargetInterval ny))
    (initial : Fin M → TargetInterval ny → ℚ) (i : Fin M)
    (hM : 0 < M) (hPpos : 0 < P)
    (hbPower : ∃ e : ℕ, b = 2 ^ e) (hPPower : ∃ e : ℕ, P = 2 ^ e)
    (hscale : (M : ℚ) ≤ (2 : ℚ) ^ (-(thetaExponent : ℤ)) * P) :
    seedGridSpacing b P ∣ bandRoundSpacing thetaExponent b band initial i := by
  let theta : ℚ := 2 ^ (-(thetaExponent : ℤ))
  have htheta : 0 ≤ theta := (zpow_pos (by norm_num : (0 : ℚ) < 2) _).le
  have hMr : (0 : ℚ) < M := by exact_mod_cast hM
  have hPr : (0 : ℚ) < P := by exact_mod_cast hPpos
  have hratio : (M : ℚ) / P ≤ theta := (div_le_iff₀ hPr).2 hscale
  have hfloor : (b : ℚ) / P ≤ theta * ((b : ℚ) / M) := by
    calc
      _ = ((b : ℚ) / M) * ((M : ℚ) / P) := by field_simp [hMr.ne', hPr.ne']
      _ ≤ ((b : ℚ) / M) * theta :=
        mul_le_mul_of_nonneg_left hratio (div_nonneg (Nat.cast_nonneg _) hMr.le)
      _ = _ := mul_comm _ _
  have henvelope := (bandChildEnvelope_lower b band initial i).1
  have hproduct := hfloor.trans (mul_le_mul_of_nonneg_left henvelope htheta)
  have hwide : (seedGridSpacing b P : ℚ) ≤
      max 1 (theta * bandChildEnvelope b band initial i) := by
    unfold seedGridSpacing
    rw [Nat.cast_max, Nat.cast_one]
    exact max_le_max le_rfl ((Nat.cast_div_le (m := b) (n := P)).trans hproduct)
  have hspacing := bandRoundSpacing_exact thetaExponent b band initial i
  have hle : seedGridSpacing b P ≤ bandRoundSpacing thetaExponent b band initial i := by
    have h := hwide.trans_eq hspacing.symm
    exact_mod_cast h
  exact dyadic_dvd_of_le (seedGridSpacing_dyadic hbPower hPPower)
    ⟨_, rfl⟩ hle

end EditApproximation

end OAI
