import Mathlib.Tactic.FinCases
import OAI.NumberTheory.Catalan.FiniteMatrices.FixedCanonicalModularForm
import OAI.NumberTheory.Catalan.FiniteMatrices.FixedLiteralBaseRelationsRows0To1

namespace OAI

section

noncomputable section
namespace InternalCatalan

theorem fixedIntegerBaseCanonical_mod_row_35 (k : Fin 48) :
    (fixedIntegerBaseCanonical (35 : Fin 49) k : ZMod 101) =
      fixedLiteralBaseMod (35 : Fin 49) k := by
  rw [fixedIntegerBaseCanonical_mod_coefficients]
  revert k
  decide +kernel

end InternalCatalan

end

end

end OAI
