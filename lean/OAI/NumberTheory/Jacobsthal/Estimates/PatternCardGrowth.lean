import OAI.NumberTheory.Jacobsthal.Probability.SourceFullEventCount

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Filter
namespace ErdosVarianceLargeMap
open NumberTheoryLean ErdosVarianceSmallModel ErdosVarianceLargeCount ErdosInverseEuler ErdosInverseBoxHeight

theorem patternCard_le_smallModulus_sq (w : ℝ) (H : ℕ) :
    patternCard (divisorModulus w H) (coprimeModulus w H) ≤ (smallModulus w)^2 := by
  let T0 := divisorModulus w H
  let T1 := coprimeModulus w H
  calc
    _ = (T0*T1)*(T0.totient*T1.totient) := by unfold patternCard;ring
    _ ≤ (T0*T1)*(T0*T1) := Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.totient_le _) (Nat.totient_le _))
    _ = (smallModulus w)^2 := by rw [pattern_moduli_product,pow_two]

theorem source_patternCard_Z : ∀ᶠ z : ℝ in atTop,∀ H : ℕ,
    (patternCard (divisorModulus (sourceW z) H) (coprimeModulus (sourceW z) H) : ℝ) ≤ sourceZ z := by
  filter_upwards [smallModulus_source_power 2 1 zero_lt_one] with z hz
  intro H
  have hh : (patternCard (divisorModulus (sourceW z) H) (coprimeModulus (sourceW z) H) : ℝ) ≤
      (smallModulus (sourceW z) : ℝ)^2 := by exact_mod_cast patternCard_le_smallModulus_sq (sourceW z) H
  exact hh.trans (by simpa only [Real.rpow_one] using hz)

end ErdosVarianceLargeMap

end

end Erdos970

end OAI
