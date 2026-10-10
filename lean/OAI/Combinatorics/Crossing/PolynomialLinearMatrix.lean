import OAI.Combinatorics.Crossing.PolynomialCoordinates

namespace OAI

noncomputable section
namespace Zarankiewicz
open PolynomialModule Module
variable {V W ι κ : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
variable [Fintype ι] [Fintype κ] [DecidableEq κ]

def polynomialLinearMatrix (bV : Basis κ ℝ V) (bW : Basis ι ℝ W)
    (F : V →ₗ[ℝ] PolynomialModule ℝ W) : Matrix ι κ (Polynomial ℝ) :=
  polynomialColumnMatrix bW (fun j => F (bV j))

theorem polynomialLinearMatrix_eval (bV : Basis κ ℝ V) (bW : Basis ι ℝ W)
    (F : V →ₗ[ℝ] PolynomialModule ℝ W) (t : ℝ) :
    (polynomialLinearMatrix bV bW F).map (Polynomial.eval t) =
      LinearMap.toMatrix bV bW ((eval t).comp F) := by
  funext i j
  rw [LinearMap.toMatrix_apply]
  exact polynomialColumnMatrix_eval bW (fun j => F (bV j)) t i j

theorem polynomialLinearMatrix_rank (bV : Basis κ ℝ V) (bW : Basis ι ℝ W)
    (F : V →ₗ[ℝ] PolynomialModule ℝ W) (t : ℝ) :
    ((polynomialLinearMatrix bV bW F).map (Polynomial.eval t)).rank =
      finrank ℝ (LinearMap.range ((eval t).comp F)) := by
  rw [polynomialLinearMatrix_eval, Matrix.rank_eq_finrank_range_toLin _ bW bV,
    Matrix.toLin_toMatrix]

end Zarankiewicz

end

end OAI
