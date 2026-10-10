import OAI.NumberTheory.CubicMoment.Angular.AngularKummerPrimeSum

namespace OAI

/-! The literal angular cubic character, with the argument order of the
cubic residue symbol. Only multiplicativity in the prime variable is used;
the fixed angular factor is not duplicated in the numerator variable. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def angularCubicSymbol (ℓ : ℤ) (a v : Eisenstein) : ℂ :=
  angularKummerCharacter ℓ v a

lemma angularCubicSymbol_mul_lower (ℓ : ℤ) {a b : Eisenstein}
    (ha : a ≠ 0) (hb : b ≠ 0) (v : Eisenstein) :
    angularCubicSymbol ℓ (a*b) v = angularCubicSymbol ℓ a v*angularCubicSymbol ℓ b v := by
  simp only [angularCubicSymbol,angularKummerCharacter,theta_mul,
    cubicSymbol_mul_lower ha hb]
  ring

lemma angularCubicSymbol_norm_le_one (ℓ : ℤ) {a : Eisenstein}
    (ha : primary a) (v : Eisenstein) : ‖angularCubicSymbol ℓ a v‖ ≤ 1 :=
  angularKummerCharacter_norm_le_one ℓ v ha

end CubicFirstMoment

end

end OAI
