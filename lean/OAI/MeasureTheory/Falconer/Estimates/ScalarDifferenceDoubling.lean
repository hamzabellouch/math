import OAI.MeasureTheory.Falconer.Estimates.ScalarPluennecke

namespace OAI

/-! A small difference set supplies the doubling bound needed by
coefficient arithmetic. -/
namespace Falconer
open scoped Pointwise

 theorem scalar_doubling_of_difference (δ : ℝ) (A : Finset ℝ)
    (hA : A.Nonempty) {K : ℝ}
    (hsmall : ((scalarCells δ (A-A)).card : ℝ) ≤ K*(scalarCells δ A).card) :
    ((scalarCells δ (A+A)).card : ℝ) ≤ 16*K^2*(scalarCells δ A).card := by
  have hAB : ((scalarCells δ (A+(-A))).card : ℝ) ≤ K*(scalarCells δ A).card := by
    simpa only [← sub_eq_add_neg] using hsmall
  have hh := scalar_pluennecke δ A (-A) hA hAB 0 2
  have he : (0 : ℕ) • (-A)-(2 : ℕ) • (-A) = A+A := by
    simp only [zero_nsmul,two_nsmul,zero_sub,neg_add,neg_neg]
  rw [he] at hh
  norm_num only [Nat.cast_zero,Nat.cast_ofNat,zero_add] at hh
  convert hh using 1
  ring

end Falconer

end OAI
