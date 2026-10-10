import Mathlib
import OAI.Analysis.Conductivity.Variational.SynchronizedChartWaves

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Matrix
open scoped Matrix.Norms.Elementwise

lemma symmetric_matrix_bounded_of_quadratic (A : Mat3) (hA : A.IsSymm)
    {C : ℝ} (hC : 0≤C)
    (hb : ∀ v : Coord3,0≤v ⬝ᵥ(A*ᵥv) ∧ v ⬝ᵥ(A*ᵥv)≤C*‖v‖^2) :
    ‖A‖≤3*C := by
  have hn (i : Fin 3) : ‖(Pi.single i 1 : Coord3)‖=1 := by rw [Pi.norm_single]; norm_num
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0≤3*C)).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0≤3*C)).mpr
  intro j
  have hi := hb (Pi.single i 1)
  have hj := hb (Pi.single j 1)
  have hij := hb (Pi.single i 1+Pi.single j 1)
  have hnij : ‖(Pi.single i 1+Pi.single j 1 : Coord3)‖≤2 := by
    calc
      _ ≤ ‖(Pi.single i 1 : Coord3)‖+‖(Pi.single j 1 : Coord3)‖ := norm_add_le _ _
      _ = 2 := by rw [hn,hn]; norm_num
  have hnsq : ‖(Pi.single i 1+Pi.single j 1 : Coord3)‖^2≤4 := by
    nlinarith [norm_nonneg (Pi.single i 1+Pi.single j 1 : Coord3)]
  have hsq := mul_le_mul_of_nonneg_left hnsq hC
  have hs : A j i=A i j := congrFun (congrFun hA i) j
  simp only [Matrix.mulVec_add,dotProduct_add,add_dotProduct,
    Matrix.mulVec_single,single_dotProduct,one_mul,
    hn,one_pow,mul_one,Matrix.col_apply,
    show MulOpposite.op (1:ℝ)=(1:ℝᵐᵒᵖ) from rfl,one_smul] at hi hj hij
  rw [hs] at hij
  rw [Real.norm_eq_abs,abs_le]
  constructor <;> nlinarith

end ScalarConductivity

end
end

end OAI
