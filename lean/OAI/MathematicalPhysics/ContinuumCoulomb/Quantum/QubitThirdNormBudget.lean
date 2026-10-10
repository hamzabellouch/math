import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QubitMediatorNormBounds
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumThirdCounterterm

namespace OAI

/-! A rational polynomial budget for the third-order counterterms. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def qmaThirdWeight (j : ℝ) : ℝ := (1+|j|)^2

theorem qmaThirdWeight_bounds (j : ℝ) :
    1 ≤ qmaThirdWeight j ∧ |j| ≤ qmaThirdWeight j ∧
      1+(j/2)^2+|j| ≤ qmaThirdWeight j ∧
      1+|j|/2 ≤ 1+|j| := by
  have hj := abs_nonneg j
  have hs := sq_abs j
  dsimp [qmaThirdWeight]
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem qmaMatrix_real_smul_norm (r : ℝ) (M : Matrix σ σ ℂ) :
    ‖spinMatrixOperator (r • M)‖ = |r| * ‖spinMatrixOperator M‖ := by
  change ‖spinMatrixOperator ((r:ℂ) • M)‖ = _
  rw [spinMatrixOperator_smul,norm_smul,Complex.norm_real,Real.norm_eq_abs]

theorem qmaMatrix_product_norm (A B : Matrix σ σ ℂ)
    (hA : ‖spinMatrixOperator A‖ ≤ 1) (hB : ‖spinMatrixOperator B‖ ≤ 1) :
    ‖spinMatrixOperator (A*B)‖ ≤ 1 := by
  rw [spinMatrixOperator_mul]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul hA hB (norm_nonneg _) zero_le_one).trans_eq (one_mul _))

theorem qmaMatrixOperator_neg (A : Matrix σ σ ℂ) :
    spinMatrixOperator (-A) = -spinMatrixOperator A := by
  unfold spinMatrixOperator
  rw [map_neg,map_neg]

theorem qmaThirdPair_norm (A B : Matrix σ σ ℂ) (j : ℝ)
    (hA : ‖spinMatrixOperator A‖ ≤ 1) (hB : ‖spinMatrixOperator B‖ ≤ 1) :
    ‖spinMatrixOperator (qmaThirdSeriesPair A B j)‖ ≤ 1+|j| := by
  have he : (j:ℂ)/2 = ((j/2:ℝ):ℂ) := by push_cast; rfl
  unfold qmaThirdSeriesPair
  rw [he,spinMatrixOperator_add,spinMatrixOperator_smul]
  calc
    _ ≤ ‖spinMatrixOperator A‖+‖((j/2:ℝ):ℂ) • spinMatrixOperator B‖ := norm_add_le _ _
    _ = ‖spinMatrixOperator A‖+(|j|/2)*‖spinMatrixOperator B‖ := by
      rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_div,
        abs_of_pos (by norm_num : (0:ℝ) < 2)]
    _ ≤ 1+|j|/2 := by
      simpa only [mul_one] using add_le_add hA (mul_le_mul_of_nonneg_left hB (by positivity))
    _ ≤ 1+|j| := (qmaThirdWeight_bounds j).2.2.2

theorem qmaThirdCounter_norm (A B C : Matrix σ σ ℂ) (r j : ℝ) (hr : 0 ≤ r)
    (hA : ‖spinMatrixOperator A‖ ≤ 1) (hB : ‖spinMatrixOperator B‖ ≤ 1)
    (hC : ‖spinMatrixOperator C‖ ≤ 1) :
    ‖spinMatrixOperator (qmaThirdSeriesCounter A B C r j)‖ ≤ (r+1)*qmaThirdWeight j := by
  let c : ℝ := 1+(j/2)^2
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hcast : (1+((j:ℂ)/2)^2) = (c:ℂ) := by dsimp [c]; push_cast; rfl
  have hI : ‖spinMatrixOperator (1 : Matrix σ σ ℂ)‖ ≤ 1 := by
    exact spinMatrixOperator_unitary_norm _ (by simp)
  have hAB := qmaMatrix_product_norm A B hA hB
  have he : qmaThirdSeriesCounter A B C r j =
      (r:ℝ) • ((c:ℝ) • (1 : Matrix σ σ ℂ)+(j:ℝ) • (A*B))-(c:ℝ) • C := by
    simp only [qmaThirdSeriesCounter,hcast]
    rfl
  rw [he]
  have hfirst : ‖spinMatrixOperator ((c:ℝ) • (1 : Matrix σ σ ℂ)+(j:ℝ) • (A*B))‖ ≤ c+|j| := by
    rw [spinMatrixOperator_add]
    apply (norm_add_le _ _).trans
    rw [qmaMatrix_real_smul_norm,qmaMatrix_real_smul_norm,abs_of_nonneg hc]
    simpa only [mul_one] using add_le_add
      (mul_le_mul_of_nonneg_left hI hc) (mul_le_mul_of_nonneg_left hAB (abs_nonneg j))
  have hnormsub : ‖spinMatrixOperator (r • (c • (1 : Matrix σ σ ℂ)+j • (A*B))-c • C)‖ ≤
      ‖spinMatrixOperator (r • (c • (1 : Matrix σ σ ℂ)+j • (A*B)))‖+
      ‖spinMatrixOperator (c • C)‖ := by
    rw [sub_eq_add_neg]
    rw [spinMatrixOperator_add]
    rw [qmaMatrixOperator_neg]
    simpa only [norm_neg] using norm_add_le (spinMatrixOperator (r • (c • (1 : Matrix σ σ ℂ)+j • (A*B))))
      (-(spinMatrixOperator (c • C)))
  apply hnormsub.trans
  rw [qmaMatrix_real_smul_norm,qmaMatrix_real_smul_norm,abs_of_nonneg hr,abs_of_nonneg hc]
  calc
    _ ≤ r*(c+|j|)+c := by
      simpa only [mul_one] using add_le_add (mul_le_mul_of_nonneg_left hfirst hr)
        (mul_le_mul_of_nonneg_left hC hc)
    _ ≤ (r+1)*qmaThirdWeight j := by
      have hb := (qmaThirdWeight_bounds j).2.2.1
      change c+|j| ≤ qmaThirdWeight j at hb
      have hm := mul_le_mul_of_nonneg_left hb hr
      nlinarith [abs_nonneg j]

end ContinuumCoulomb

end

end OAI
