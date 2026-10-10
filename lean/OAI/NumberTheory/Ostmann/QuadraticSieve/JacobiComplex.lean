import OAI.NumberTheory.Ostmann.QuadraticSieve.JacobiCharacter
import OAI.NumberTheory.Ostmann.QuadraticSieve.WeightedJacobiMoment

namespace OAI

/-! # The concrete complex Jacobi character used in the Fourier expansion -/

namespace Ostmann

noncomputable def jacobiComplex (M : ℕ) [NeZero M] : DirichletCharacter ℂ M :=
  (jacobiCharacterInt M).ringHomComp (Int.castRingHom ℂ)

theorem jacobiComplex_natCast (M : ℕ) [NeZero M] (s : ℕ) :
    jacobiComplex M (s : ZMod M) = (realJacobi s M : ℂ) := by
  change ((jacobiCharacterInt M) (s : ZMod M) : ℂ) = ((jacobiSym (s : ℤ) M : ℝ) : ℂ)
  rw [← Int.cast_natCast s, jacobiCharacterInt_intCast]
  simp

theorem jacobiComplex_isQuadratic (M : ℕ) [NeZero M] : (jacobiComplex M).IsQuadratic := by
  apply MulChar.IsQuadratic.comp
  intro a
  change jacobiSym (a.val : ℤ) M = 0 ∨ jacobiSym (a.val : ℤ) M = 1 ∨ jacobiSym (a.val : ℤ) M = -1
  rcases jacobiSym.trichotomy (a.val : ℤ) M with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

end Ostmann

end OAI
