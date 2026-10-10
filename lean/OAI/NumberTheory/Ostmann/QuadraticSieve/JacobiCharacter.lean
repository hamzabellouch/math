import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

namespace OAI

/-! # The concrete Dirichlet character with Jacobi numerator -/

namespace Ostmann

noncomputable def jacobiResidue (N : ℕ) (a : ZMod N) : ℤ := jacobiSym (a.val : ℤ) N

theorem jacobiResidue_intCast (N : ℕ) [NeZero N] (a : ℤ) :
    jacobiResidue N (a : ZMod N) = jacobiSym a N := by
  unfold jacobiResidue
  rw [ZMod.val_intCast]
  exact (jacobiSym.mod_left a N).symm

/-- This definition includes the modulus-one character. The nonunit values
vanish by the gcd criterion for Jacobi symbols. -/
noncomputable def jacobiCharacterInt (N : ℕ) [NeZero N] : DirichletCharacter ℤ N where
  toFun := jacobiResidue N
  map_one' := by simpa using jacobiResidue_intCast N 1
  map_mul' := by
    intro a b
    have hm : (((a.val : ℤ) * (b.val : ℤ) : ℤ) : ZMod N) = a * b := by
      simp only [Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
    calc
      jacobiResidue N (a * b) = jacobiResidue N (((a.val : ℤ) * (b.val : ℤ) : ℤ) : ZMod N) :=
        congrArg (jacobiResidue N) hm.symm
      _ = jacobiSym ((a.val : ℤ) * (b.val : ℤ)) N := jacobiResidue_intCast N _
      _ = jacobiResidue N a * jacobiResidue N b := jacobiSym.mul_left _ _ _
  map_nonunit' := by
    intro a ha
    unfold jacobiResidue
    apply jacobiSym.eq_zero_iff_not_coprime.mpr
    intro hc
    have hcop : a.val.Coprime N := by simpa only [Int.gcd_natCast_natCast] using hc
    have hu := (ZMod.isUnit_iff_coprime a.val N).mpr hcop
    rw [ZMod.natCast_zmod_val] at hu
    exact ha hu

@[simp] theorem jacobiCharacterInt_intCast (N : ℕ) [NeZero N] (a : ℤ) :
    jacobiCharacterInt N (a : ZMod N) = jacobiSym a N := jacobiResidue_intCast N a

noncomputable def jacobiCharacter (N : ℕ) [NeZero N] : DirichletCharacter ℝ N :=
  (jacobiCharacterInt N).ringHomComp (Int.castRingHom ℝ)

@[simp] theorem jacobiCharacter_intCast (N : ℕ) [NeZero N] (a : ℤ) :
    jacobiCharacter N (a : ZMod N) = (jacobiSym a N : ℝ) := by
  simp [jacobiCharacter, MulChar.ringHomComp_apply]

@[simp] theorem jacobiCharacter_natCast (N : ℕ) [NeZero N] (a : ℕ) :
    jacobiCharacter N (a : ZMod N) = (jacobiSym (a : ℤ) N : ℝ) := by
  simpa only [Int.cast_natCast] using jacobiCharacter_intCast N (a : ℤ)

end Ostmann

end OAI
