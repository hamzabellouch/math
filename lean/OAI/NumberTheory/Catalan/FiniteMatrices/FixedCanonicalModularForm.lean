import OAI.NumberTheory.Catalan.Arithmetic.FixedCanonicalIntegerBase
import OAI.NumberTheory.Catalan.Polynomial.FixedCanonicalCoefficientTables

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace InternalCatalan

theorem fixedIntegerBaseCanonical_mod_coefficients (r : Fin 49) (k : Fin 48) :
    (fixedIntegerBaseCanonical r k : ZMod 101) =
      2 * (∑ i ∈ Finset.range 65,
        (fixedCanonicalPCoeff r i : ZMod 101) * (fixedClearedMoment i k : ZMod 101)) -
      3 * (∑ i ∈ Finset.range 65,
        (fixedCanonicalDCoeff r i : ZMod 101) * (fixedClearedZeta i k : ZMod 101)) := by
  simp only [fixedIntegerBaseCanonical, fixedCanonicalPCoeff_eq, fixedCanonicalDCoeff_eq,
    Int.cast_sub, Int.cast_mul, Int.cast_sum, Int.cast_ofNat]

end InternalCatalan

end

end

end OAI
