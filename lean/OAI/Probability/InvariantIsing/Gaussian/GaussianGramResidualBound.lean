import OAI.Probability.InvariantIsing.Gaussian.GaussianGramQuadraticError
import OAI.Probability.InvariantIsing.Gaussian.MarchenkoPasturTransform

namespace OAI

/-! A pathwise residual bound for the finite Gaussian Gram transform equation. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace InvariantIsing

theorem gaussianGramResidual_bound {N m : ℕ} (hN : 0 < N) {t : ℝ} (ht : 0 < t)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) :
    |marchenkoPasturResidual t ((m : ℝ)/N) (gaussianGramStieltjes t z)| ≤
      (1/(N : ℝ))*∑ j : Fin m, (gaussianGramColumnDeviation t z j+1/((N : ℝ)*t)) := by
  let u := gaussianGramStieltjes t z
  let q := fun j : Fin m => gaussianGramColumnQuadratic t z j
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hu : 0 ≤ u := gaussianGramStieltjes_nonneg ht z
  have hq : ∀ j, 0 ≤ q j := gaussianGramColumnQuadratic_nonneg ht z
  have he := gaussianGramStieltjes_column_equation hN ht z
  have hsum : marchenkoPasturResidual t ((m : ℝ)/N) u =
      (1/(N : ℝ))*∑ j : Fin m, (q j/(1+q j)-u/(1+u)) := by
    unfold marchenkoPasturResidual
    rw [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    change 1-t*u = (1/(N : ℝ))*∑ j, q j/(1+q j) at he
    rw [he]
    ring
  rw [hsum,abs_mul,abs_of_pos (one_div_pos.mpr hn)]
  apply mul_le_mul_of_nonneg_left _ (one_div_pos.mpr hn).le
  calc
    _ ≤ ∑ j, |q j/(1+q j)-u/(1+u)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |q j-u| := Finset.sum_le_sum (fun j _ => nonnegative_fraction_lipschitz (hq j) hu)
    _ ≤ _ := Finset.sum_le_sum (fun j _ => gaussianGramColumnQuadratic_error hN ht z j)

end InvariantIsing

end

end OAI
