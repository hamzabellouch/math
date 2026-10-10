import Mathlib.Data.ZMod.Basic
import OAI.NumberTheory.Ostmann.Arithmetic.ArithmeticPrecision

namespace OAI

/-! # Division by a signed frequency with an explicit loss of precision

The quotient is an actual function on residue classes. It agrees with
integer division whenever the frequency divides the represented integer.
-/

namespace Ostmann

theorem modEq_divide_signed {s a b : ℤ} (M : ℕ) (hs : s ≠ 0)
    (ha : s ∣ a) (hb : s ∣ b)
    (h : a ≡ b [ZMOD (s.natAbs * M : ℕ)]) :
    a / s ≡ b / s [ZMOD M] := by
  apply Int.modEq_iff_dvd.mpr
  apply Int.dvd_of_mul_dvd_mul_left hs
  rw [mul_sub, Int.mul_ediv_cancel' hb, Int.mul_ediv_cancel' ha]
  apply dvd_trans _ h.dvd
  have hsabs : s ∣ (s.natAbs : ℤ) := Int.dvd_natCast.mpr (dvd_refl _)
  simpa only [Nat.cast_mul] using mul_dvd_mul_right hsabs (M : ℤ)

noncomputable def residueQuotient (s : ℤ) (M : ℕ)
    (x : ZMod (s.natAbs * M)) : ZMod M :=
  ((x.val : ℤ) / s : ℤ)

theorem residueQuotient_intCast (s : ℤ) (M : ℕ) [NeZero M]
    (hs : s ≠ 0) (a : ℤ) (ha : s ∣ a) :
    residueQuotient s M (a : ZMod (s.natAbs * M)) = (a / s : ℤ) := by
  have : NeZero (s.natAbs * M) :=
    ⟨mul_ne_zero (Int.natAbs_ne_zero.mpr hs) (NeZero.ne M)⟩
  have hmod : ((a : ZMod (s.natAbs * M)).val : ℤ) ≡ a
      [ZMOD (s.natAbs * M : ℕ)] := by
    apply (ZMod.intCast_eq_intCast_iff _ _ _).mp
    simp only [Int.cast_natCast, ZMod.natCast_zmod_val]
  have hval : s ∣ ((a : ZMod (s.natAbs * M)).val : ℤ) := by
    have hsabs : s ∣ (s.natAbs : ℤ) := Int.dvd_natCast.mpr (dvd_refl _)
    have hdiv : s ∣ a - ((a : ZMod (s.natAbs * M)).val : ℤ) :=
      dvd_trans (dvd_mul_of_dvd_left hsabs (M : ℤ)) hmod.dvd
    simpa only [sub_sub_cancel] using dvd_sub ha hdiv
  exact (ZMod.intCast_eq_intCast_iff _ _ _).mpr
    (modEq_divide_signed M hs hval ha hmod)

noncomputable def frequencyQuotient (R M : ℕ) (s : ℤ)
    (hsR : s.natAbs ∣ R) (x : ZMod (R * M)) : ZMod M :=
  residueQuotient s M
    (ZMod.castHom (Nat.mul_dvd_mul hsR (dvd_refl M)) _ x)

theorem frequencyQuotient_intCast (R M : ℕ) [NeZero M] (s : ℤ)
    (hs : s ≠ 0) (hsR : s.natAbs ∣ R) (a : ℤ) (ha : s ∣ a) :
    frequencyQuotient R M s hsR (a : ZMod (R * M)) = (a / s : ℤ) := by
  rw [frequencyQuotient, map_intCast]
  exact residueQuotient_intCast s M hs a ha

/-- The extra compensation factor is a unit, so it costs no further
precision after the signed frequency has been divided out. -/
theorem frequencyQuotient_reversal (R M : ℕ) [NeZero M] (s : ℤ)
    (hs : s ≠ 0) (hsR : s.natAbs ∣ R) (u p : ℤ)
    (U : (ZMod M)ˣ) (hU : (U : ZMod M) = u) :
    frequencyQuotient R M s hsR (s * u * p : ZMod (R * M)) * ↑U⁻¹ = p := by
  have h := frequencyQuotient_intCast R M s hs hsR (s * u * p)
    (dvd_mul_of_dvd_left (dvd_mul_right s u) p)
  have hdiv : (s * u * p) / s = u * p := by
    rw [Int.mul_assoc, Int.mul_ediv_cancel_left _ hs]
  rw [hdiv] at h
  simp only [Int.cast_mul] at h
  rw [h, ← hU]
  calc
    (U : ZMod M) * p * ↑U⁻¹ = (p : ZMod M) * ((U : ZMod M) * ↑U⁻¹) := by ring
    _ = p := by rw [U.mul_inv, mul_one]

end Ostmann

end OAI
