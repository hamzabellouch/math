import Mathlib

namespace OAI
noncomputable section

namespace Problem337

/-- The standard additive character evaluated at a natural integer. -/
lemma stdAddChar_natCast {q : ℕ} [NeZero q] (z : ℕ) :
    ZMod.stdAddChar (z : ZMod q) =
      Complex.exp (2 * Real.pi * Complex.I * (z : ℂ) / (q : ℂ)) := by
  simpa using ZMod.stdAddChar_coe (N := q) (z : ℤ)

/-- Cancelling an integer common factor in the numerator and modulus does not
change the additive phase. -/
lemma stdAddChar_cancel_factor {g q : ℕ} [NeZero g] [NeZero q]
    [NeZero (g * q)] (c z : ℕ) :
    ZMod.stdAddChar ((g * c * z : ℕ) : ZMod (g * q)) =
      ZMod.stdAddChar ((c * z : ℕ) : ZMod q) := by
  rw [stdAddChar_natCast, stdAddChar_natCast]
  congr 1
  push_cast
  have hg : (g : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne g
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  field_simp

lemma reduced_modulus_pos (a u : ℕ) (hu : 0 < u) :
    0 < u / a.gcd u :=
  Nat.div_pos (Nat.gcd_le_right a hu) (Nat.gcd_pos_of_pos_right a hu)

/-- After cancelling the gcd, the numerator is an invertible residue class. -/
def reducedFrequency (a u : ℕ) (hu : 0 < u) : (ZMod (u / a.gcd u))ˣ :=
  ZMod.unitOfCoprime (a / a.gcd u)
    (Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_right a hu))

@[simp] lemma reducedFrequency_coe (a u : ℕ) (hu : 0 < u) :
    (reducedFrequency a u hu : ZMod (u / a.gcd u)) = (a / a.gcd u : ℕ) :=
  ZMod.coe_unitOfCoprime _ _

/-- Exact phase reduction to a primitive (unit-frequency) character. This also
covers `a = 0`, where the reduced modulus is `1`. -/
theorem stdAddChar_reduced (a u z : ℕ) (hu : 0 < u)
    [NeZero u] [NeZero (u / a.gcd u)] :
    ZMod.stdAddChar ((a * z : ℕ) : ZMod u) =
      ZMod.stdAddChar ((reducedFrequency a u hu : ZMod (u / a.gcd u)) *
        (z : ZMod (u / a.gcd u))) := by
  rw [reducedFrequency_coe, ← Nat.cast_mul]
  rw [stdAddChar_natCast, stdAddChar_natCast]
  congr 1
  have hgu : a.gcd u * (u / a.gcd u) = u :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_right a u)
  have hga : a.gcd u * (a / a.gcd u) = a :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_left a u)
  have hguC : (a.gcd u : ℂ) * ((u / a.gcd u : ℕ) : ℂ) = (u : ℂ) := by
    exact_mod_cast hgu
  have hgaC : (a.gcd u : ℂ) * ((a / a.gcd u : ℕ) : ℂ) = (a : ℂ) := by
    exact_mod_cast hga
  push_cast
  rw [← hguC, ← hgaC]
  have hg : (a.gcd u : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.gcd_pos_of_pos_right a hu).ne'
  have hq : ((u / a.gcd u : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (reduced_modulus_pos a u hu).ne'
  field_simp

end Problem337

end

end OAI
