import OAI.Algebra.FormulaHitting.System
import OAI.Algebra.FormulaHitting.FormulaSeries

namespace OAI

namespace NCHitting

theorem Formula.system_output_eq_series {F : Type*} {n : ℕ}
    [Field F] [CharZero F] (f : Formula F n) :
    f.representation.contract f.representation.fundamentalMatrix = f.series := by
  rw [f.system_output, f.series_eq_sum_of_cutoff
    (Fintype.card f.representation.State) f.coeff_zero_of_representation_dimension_le]

end NCHitting

end OAI
