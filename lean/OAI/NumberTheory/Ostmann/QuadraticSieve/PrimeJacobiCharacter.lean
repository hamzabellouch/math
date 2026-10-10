import OAI.NumberTheory.Ostmann.QuadraticSieve.JacobiCharacter

namespace OAI

/-! # The prime-level Jacobi character is primitive -/

namespace Ostmann

theorem jacobiCharacterInt_prime (p : ℕ) [Fact p.Prime] :
    jacobiCharacterInt p = quadraticChar (ZMod p) := by
  apply MulChar.ext
  intro a
  have hcast : ((((a : ZMod p).val : ℤ) : ZMod p)) = (a : ZMod p) := by
    simp only [Int.cast_natCast, ZMod.natCast_zmod_val]
  calc
    jacobiCharacterInt p a = jacobiCharacterInt p ((((a : ZMod p).val : ℤ) : ZMod p)) :=
      congrArg (jacobiCharacterInt p) hcast.symm
    _ = jacobiSym ((a : ZMod p).val : ℤ) p := jacobiCharacterInt_intCast p _
    _ = legendreSym p ((a : ZMod p).val : ℤ) := (jacobiSym.legendreSym.to_jacobiSym p _).symm
    _ = quadraticChar (ZMod p) a := by rw [legendreSym, hcast]

theorem jacobiCharacter_prime_ne_one (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    jacobiCharacter p ≠ 1 := by
  have hc : ringChar (ZMod p) ≠ 2 := by simpa only [ZMod.ringChar_zmod_n] using hp2
  obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one' hc
  intro he
  have hev := congrArg (fun χ : DirichletCharacter ℝ p => χ a) he
  have hneg : jacobiCharacter p a = -1 := by
    simp only [jacobiCharacter, MulChar.ringHomComp_apply, jacobiCharacterInt_prime]
    rw [ha]
    norm_num
  rw [hneg, MulChar.one_apply a.isUnit] at hev
  norm_num at hev

theorem jacobiCharacter_prime_primitive (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    (jacobiCharacter p).IsPrimitive := by
  have hc := (jacobiCharacter p).conductor_dvd_level
  have hn : (jacobiCharacter p).conductor ≠ 1 := fun he =>
    jacobiCharacter_prime_ne_one p hp2 (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr he)
  exact ((Fact.out : p.Prime).eq_one_or_self_of_dvd _ hc).resolve_left hn

end Ostmann

end OAI
