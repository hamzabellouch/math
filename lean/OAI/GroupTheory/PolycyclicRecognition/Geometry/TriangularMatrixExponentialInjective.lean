import OAI.GroupTheory.PolycyclicRecognition.Geometry.TriangularExponentialInjective
import OAI.GroupTheory.PolycyclicRecognition.Geometry.AlgebraExponential

namespace OAI

/-! # Injectivity on upper triangular real matrices -/

noncomputable section
namespace PolycyclicRecognition
open scoped Matrix.Norms.Operator

theorem triangularMatrix_exp_injective {m : ℕ}
    {x y : Matrix (Fin m) (Fin m) ℝ}
    (hx : x.IsUpperTriangular) (hy : y.IsUpperTriangular)
    (h : NormedSpace.exp x = NormedSpace.exp y) : x = y := by
  let X : RealTriangularAlgebra m := ⟨x,hx⟩
  let Y : RealTriangularAlgebra m := ⟨y,hy⟩
  have he : NormedSpace.exp X = NormedSpace.exp Y := by
    apply Subtype.ext
    simpa only [realTriangularAlgebra_coe_exp] using h
  exact congrArg Subtype.val (realTriangularAlgebra_exp_injective m he)

theorem triangular_units_product_eq_one_imp_neg {L : Type*}
    [AddCommGroup L] [Module ℝ L] {m : ℕ}
    (j : L →ₗ[ℝ] Matrix (Fin m) (Fin m) ℝ) (hj : Function.Injective j)
    (hu : ∀ x, (j x).IsUpperTriangular) (x y : L)
    (h : algebraExpUnit (j x) * algebraExpUnit (j y) = 1) : x = -y := by
  have hm : algebraExpUnit (j x) = algebraExpUnit (-j y) := by
    rw [algebraExpUnit_neg]
    exact eq_inv_of_mul_eq_one_left h
  have he := triangularMatrix_exp_injective (hu x) (hu y).neg (congrArg Units.val hm)
  apply hj
  simpa only [map_neg] using he

end PolycyclicRecognition

end

end OAI
