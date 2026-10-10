import OAI.Algebra.FormulaHitting.FormulaSeries
import OAI.Algebra.FormulaHitting.WordIndependence

namespace OAI

namespace NCHitting
namespace Formula

variable {F : Type*} {n : ℕ} [Field F] [CharZero F]

theorem series_eq_zero_iff (f : Formula F n) : f.series = 0 ↔ f.coeff = 0 := by
  constructor
  · intro h
    have hc : Finsupp.linearCombination F (wordSeries (F := F) (n := n))
        f.polynomial = 0 := by
      simpa only [Finsupp.linearCombination_apply] using
        (f.series_eq_smul_sum.symm.trans h)
    have hp : f.polynomial = 0 :=
      (linearIndependent_iff.mp (wordSeries_independent (F := F) (n := n))) f.polynomial hc
    funext w
    exact congrArg (fun p : Word n →₀ F => p w) hp
  · intro h
    have hp : f.polynomial = 0 := by
      ext w
      exact congrFun h w
    simp [series, hp]

theorem series_ne_zero (f : Formula F n) (hf : f.coeff ≠ 0) : f.series ≠ 0 :=
  mt f.series_eq_zero_iff.mp hf

end Formula
end NCHitting

end OAI
