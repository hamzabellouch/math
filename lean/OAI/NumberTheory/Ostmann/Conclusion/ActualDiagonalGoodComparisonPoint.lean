import OAI.NumberTheory.Ostmann.Conclusion.ActualDiagonalGoodComparisonScalar

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Conclusion

theorem diagonal_good_covariance_estimate {A m : ℝ} (hA : 0 ≤ A) (hm : 1 ≤ m)
    (j : ℕ) (x y : ℂ)
    (hr : ‖x-y‖ ≤ Real.exp (-(A+1)*m))
    (hp : ‖y‖ ≤ Real.exp (-(A+1)*(2:ℝ)^j*m)) :
    ‖x‖ ≤ Real.exp (-A*m) :=
  (norm_le_norm_sub_add x y).trans
    ((add_le_add hr hp).trans (diagonal_good_two_errors_le hA hm j))

end Ostmann.Conclusion

end

end OAI
