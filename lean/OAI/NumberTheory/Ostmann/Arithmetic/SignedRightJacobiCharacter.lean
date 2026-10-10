import OAI.NumberTheory.Ostmann.Arithmetic.SignedRightJacobiBasic

namespace OAI

namespace Ostmann.Arithmetic

noncomputable def signedRightJacobiCharacterInt (n : ℤ) (hn : n ≠ 0) :
    DirichletCharacter ℤ (4 * n.natAbs) := by
  let : NeZero (4 * n.natAbs) := ⟨mul_ne_zero (by norm_num) (Int.natAbs_ne_zero.mpr hn)⟩
  exact {
    toFun := signedRightJacobiResidue n
    map_one' := by
      simpa only [Nat.cast_one, signedRightJacobi_one] using signedRightJacobiResidue_natCast n 1
    map_mul' := by
      intro a b
      simp only [signedRightJacobiResidue, ZMod.val_mul, ← signedRightJacobi_mod, signedRightJacobi_mul]
    map_nonunit' := by
      intro a ha
      apply signedRightJacobi_zero_of_not_coprime
      intro hc
      apply ha
      simpa only [ZMod.natCast_zmod_val] using (ZMod.isUnit_iff_coprime a.val (4 * n.natAbs)).mpr hc }

@[simp] theorem signedRightJacobiCharacterInt_natCast (n : ℤ) (hn : n ≠ 0) (a : ℕ) :
    signedRightJacobiCharacterInt n hn (a : ZMod (4 * n.natAbs)) = signedRightJacobi n a :=
  signedRightJacobiResidue_natCast n a

noncomputable def signedRightJacobiCharacter (n : ℤ) (hn : n ≠ 0) :
    DirichletCharacter ℂ (4 * n.natAbs) :=
  (signedRightJacobiCharacterInt n hn).ringHomComp (Int.castRingHom ℂ)

@[simp] theorem signedRightJacobiCharacter_natCast (n : ℤ) (hn : n ≠ 0) (a : ℕ) :
    signedRightJacobiCharacter n hn (a : ZMod (4 * n.natAbs)) = (signedRightJacobi n a : ℂ) := by
  simp only [signedRightJacobiCharacter, MulChar.ringHomComp_apply,
    signedRightJacobiCharacterInt_natCast]
  rfl

theorem signedRightJacobiCharacter_natCast_of_odd (n : ℤ) (hn : n ≠ 0)
    {a : ℕ} (ha : Odd a) :
    signedRightJacobiCharacter n hn (a : ZMod (4 * n.natAbs)) = (jacobiSym n a : ℂ) := by
  simp only [signedRightJacobiCharacter_natCast, signedRightJacobi, ite_eq_left ha]

theorem signedRightJacobiCharacter_isQuadratic (n : ℤ) (hn : n ≠ 0) :
    (signedRightJacobiCharacter n hn).IsQuadratic := by
  let : NeZero (4 * n.natAbs) := ⟨mul_ne_zero (by norm_num) (Int.natAbs_ne_zero.mpr hn)⟩
  intro a
  obtain ⟨a, rfl⟩ := ZMod.natCast_zmod_surjective a
  rw [signedRightJacobiCharacter_natCast]
  rcases signedRightJacobi_trichotomy n a with h | h | h <;> simp [h]

@[simp] theorem signedRightJacobiCharacter_inv (n : ℤ) (hn : n ≠ 0) :
    (signedRightJacobiCharacter n hn)⁻¹ = signedRightJacobiCharacter n hn :=
  (signedRightJacobiCharacter_isQuadratic n hn).inv

end Ostmann.Arithmetic

end OAI
