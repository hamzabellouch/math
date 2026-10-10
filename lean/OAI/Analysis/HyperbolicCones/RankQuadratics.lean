import OAI.Analysis.HyperbolicCones.MatrixPositive
import OAI.Analysis.HyperbolicCones.PolynomialEvaluation

namespace OAI

noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator

namespace Paper256

theorem phi_rank_one_quadratic (y : Fin 3 → ℝ) (u v : Vec 4) :
    dotProduct (fun i => u i) (phi y (outer v) *ᵥ (fun i => u i)) =
      dotProduct (wedgeCoordinates v u) (qMatrix y *ᵥ wedgeCoordinates v u) := by
  rw [phi_rank_one, qMatrix_quadratic]

theorem phi_rank_one_expansion (y : Fin 3 → ℝ) (u v : Vec 4) :
    dotProduct (fun i => u i) (phi y (outer v) *ᵥ (fun i => u i)) =
      v 0 ^ 2 * dotProduct (fun i : Fin 3 => u i.succ)
        (qMatrix y *ᵥ fun i : Fin 3 => u i.succ) -
      2 * u 0 * v 0 * dotProduct (fun i : Fin 3 => u i.succ)
        (qMatrix y *ᵥ fun i : Fin 3 => v i.succ) +
      u 0 ^ 2 * dotProduct (fun i : Fin 3 => v i.succ)
        (qMatrix y *ᵥ fun i : Fin 3 => v i.succ) := by
  rw [phi_rank_one]
  simp [dotProduct, mulVec, qMatrix, wedgeCoordinates, choiLam, Fin.sum_univ_succ]
  ring

theorem phi_imaginary (y : Fin 3 → ℝ) (A : Mat 4 ℂ) :
    (phi (fun i => (y i : ℂ)) A).map Complex.im = phi y (A.map Complex.im) := by
  have hq (i j : Fin 3) : qMatrix (fun k => (y k : ℂ)) i j = ((qMatrix y i j : ℝ) : ℂ) :=
    (congrFun (congrFun (qMatrix_map Complex.ofRealHom y) i) j).symm
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;>
    refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [phi, Matrix.trace, Matrix.diag, Matrix.mul_apply, hq, Complex.mul_im]

end Paper256

end

end OAI
