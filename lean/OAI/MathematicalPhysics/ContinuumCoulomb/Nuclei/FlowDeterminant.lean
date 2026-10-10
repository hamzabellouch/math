import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.PublishedFlowInput

namespace OAI

/-! The three-dimensional Liouville determinant calculation. It remains valid
at singular matrices and at endpoints with a one-sided derivative. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

theorem flow_matrix_det_derivative
    (J : ℝ → Matrix (Fin 3) (Fin 3) ℝ) (A : Matrix (Fin 3) (Fin 3) ℝ)
    (s : Set ℝ) (t : ℝ)
    (hJ : ∀ a b, HasDerivWithinAt (fun u => J u a b) ((A * J t) a b) s t) :
    HasDerivWithinAt (fun u => (J u).det) (A.trace * (J t).det) s t := by
  have hdet := (((((hJ 0 0).mul (hJ 1 1)).mul (hJ 2 2)).sub
      (((hJ 0 0).mul (hJ 1 2)).mul (hJ 2 1))).sub
      (((hJ 0 1).mul (hJ 1 0)).mul (hJ 2 2))).add
      (((hJ 0 1).mul (hJ 1 2)).mul (hJ 2 0))
  have hdet' := (hdet.add (((hJ 0 2).mul (hJ 1 0)).mul (hJ 2 1))).sub
      (((hJ 0 2).mul (hJ 1 1)).mul (hJ 2 0))
  convert hdet' using 1
  · funext u
    exact Matrix.det_fin_three (J u)
  · simp only [Pi.mul_apply,
      Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.det_fin_three]
    ring

end ContinuumCoulomb

end

end OAI
