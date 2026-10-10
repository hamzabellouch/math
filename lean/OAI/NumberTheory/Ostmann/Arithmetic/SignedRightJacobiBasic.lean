import Mathlib

namespace OAI

namespace Ostmann.Arithmetic

def signedRightJacobi (n : ℤ) (m : ℕ) : ℤ := if Odd m then jacobiSym n m else 0

theorem signedRightJacobi_mod (n : ℤ) (m : ℕ) :
    signedRightJacobi n m = signedRightJacobi n (m % (4 * n.natAbs)) := by
  have hodd : Odd (m % (4 * n.natAbs)) ↔ Odd m := by
    rw [Nat.odd_iff, Nat.odd_iff, Nat.mod_mod_of_dvd]
    exact dvd_mul_of_dvd_left (by norm_num : 2 ∣ 4) n.natAbs
  by_cases hm : Odd m
  · simp only [signedRightJacobi, hm, hodd.mpr hm, ite_eq_left]
    exact jacobiSym.mod_right n hm
  · simp [signedRightJacobi, hm, hodd]

theorem signedRightJacobi_periodic (n : ℤ) :
    Function.Periodic (signedRightJacobi n) (4 * n.natAbs) := by
  intro m
  rw [signedRightJacobi_mod n (m + 4 * n.natAbs), Nat.add_mod_right, ← signedRightJacobi_mod]

@[simp] theorem signedRightJacobi_one (n : ℤ) : signedRightJacobi n 1 = 1 := by
  simp [signedRightJacobi]

@[simp] theorem signedRightJacobi_zero (n : ℤ) : signedRightJacobi n 0 = 0 := by
  simp [signedRightJacobi]

theorem signedRightJacobi_mul (n : ℤ) (a b : ℕ) :
    signedRightJacobi n (a * b) = signedRightJacobi n a * signedRightJacobi n b := by
  by_cases ha : Odd a
  · by_cases hb : Odd b
    · simp only [signedRightJacobi, ha, hb, ha.mul hb, ite_eq_left]
      exact jacobiSym.mul_right' n (by rintro rfl; simp at ha) (by rintro rfl; simp at hb)
    · have hab : ¬ Odd (a * b) := by simpa [Nat.odd_mul, ha] using hb
      simp [signedRightJacobi, hab, hb]
  · have hab : ¬ Odd (a * b) := by simp [Nat.odd_mul, ha]
    simp [signedRightJacobi, hab, ha]

theorem signedRightJacobi_zero_of_not_coprime (n : ℤ) (m : ℕ)
    (hc : ¬ Nat.Coprime m (4 * n.natAbs)) : signedRightJacobi n m = 0 := by
  by_cases hm : Odd m
  · simp only [signedRightJacobi, ite_eq_left hm]
    have hm4 : Nat.Coprime m 4 := by
      simpa using (Nat.coprime_two_right.mpr hm).pow_right 2
    have hmn : ¬ Nat.Coprime n.natAbs m := fun h =>
      hc (Nat.coprime_mul_iff_right.mpr ⟨hm4, h.symm⟩)
    apply jacobiSym.eq_zero_iff.mpr
    refine ⟨by rintro rfl; simp at hm, ?_⟩
    simpa only [Int.gcd_def, Int.natAbs_natCast, Nat.coprime_iff_gcd_eq_one] using hmn
  · simp only [signedRightJacobi, ite_eq_right hm]

theorem signedRightJacobi_trichotomy (n : ℤ) (m : ℕ) :
    signedRightJacobi n m = 0 ∨ signedRightJacobi n m = 1 ∨ signedRightJacobi n m = -1 := by
  unfold signedRightJacobi
  split
  · exact jacobiSym.trichotomy n m
  · exact Or.inl rfl

def signedRightJacobiResidue (n : ℤ) (a : ZMod (4 * n.natAbs)) : ℤ :=
  signedRightJacobi n a.val

@[simp] theorem signedRightJacobiResidue_natCast (n : ℤ) (a : ℕ) :
    signedRightJacobiResidue n (a : ZMod (4 * n.natAbs)) = signedRightJacobi n a := by
  rw [signedRightJacobiResidue, ZMod.val_natCast, ← signedRightJacobi_mod]

end Ostmann.Arithmetic

end OAI
