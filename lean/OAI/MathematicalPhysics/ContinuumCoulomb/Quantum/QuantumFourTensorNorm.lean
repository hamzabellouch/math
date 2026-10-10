import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFourTensorEffective
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFourCouplingBounds

namespace OAI

/-! Spectator-independent bounds for the actual many-block physical couplings. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {n : ℕ}

theorem qmaFourSpin_square (p : Fin 4) (μ : Fin 3) :
    qmaFourSpin p μ*qmaFourSpin p μ = 1 := by
  rw [qmaFourSpin_source]
  change (sourceLocalPauli 4 p μ).submatrix qmaFourBasisEquiv.symm qmaFourBasisEquiv.symm *
    (sourceLocalPauli 4 p μ).submatrix qmaFourBasisEquiv.symm qmaFourBasisEquiv.symm = 1
  rw [Matrix.submatrix_mul_equiv _ _ _ qmaFourBasisEquiv.symm _,sourceLocalPauli_sq,
    Matrix.submatrix_one_equiv]

theorem qmaFourTensorSpin_norm (i : Fin n) (p : Fin 4) (μ : Fin 3) :
    ‖spinMatrixOperator (qmaSiteMatrix i (qmaFourSpin p μ))‖ ≤ 1 := by
  apply spinMatrixOperator_unitary_norm
  rw [qmaSiteMatrix_star,qmaFourSpin_star,qmaSiteMatrix_mul,qmaFourSpin_square,qmaSiteMatrix_one]

theorem qmaFourTensorCross_norm (i j : Fin n) (p q : Fin 4) :
    ‖spinMatrixOperator (qmaFourTensorCross i j p q)‖ ≤ 3 := by
  rw [qmaFourTensorCross,spinMatrixOperator_sum]
  calc
    _ ≤ ∑ μ : Fin 3, ‖spinMatrixOperator
        (qmaSiteMatrix i (qmaFourSpin p μ)*qmaSiteMatrix j (qmaFourSpin q μ))‖ := norm_sum_le _ _
    _ ≤ ∑ _ : Fin 3, (1:ℝ) := by
      apply Finset.sum_le_sum
      intro μ _
      rw [spinMatrixOperator_mul]
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (by simpa using (mul_le_mul (qmaFourTensorSpin_norm i p μ) (qmaFourTensorSpin_norm j q μ)
          (norm_nonneg _) zero_le_one))
    _ = 3 := by norm_num

theorem qmaFourTensorWeighted_norm (i j : Fin n) (a b : Fin 4 → ℝ) :
    ‖spinMatrixOperator (qmaFourTensorWeighted i j a b)‖ ≤
      3*(∑ p, |a p|)*(∑ q, |b q|) := by
  rw [qmaFourTensorWeighted,spinMatrixOperator_sum]
  calc
    _ ≤ ∑ p, ∑ q, 3*|a p| * |b q| := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro p _
      rw [spinMatrixOperator_sum]
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro q _
      rw [spinMatrixOperator_smul,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_mul]
      calc
        _ ≤ (|a p| * |b q|)*3 := mul_le_mul_of_nonneg_left (qmaFourTensorCross_norm i j p q) (by positivity)
        _ = _ := by ring
    _ = (∑ p, 3*|a p|)*(∑ q, |b q|) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.mul_sum]
    _ = _ := by rw [← Finset.mul_sum]

theorem qmaFourTensorAxisCross_norm (i j : Fin n) (a b : Fin 2) (p q : Bool) :
    ‖spinMatrixOperator (qmaFourTensorWeighted i j (qmaFourAxisWeights a p) (qmaFourAxisWeights b q))‖ ≤
      2352 := by
  apply (qmaFourTensorWeighted_norm _ _ _ _).trans
  have ha := qmaFourAxisWeights_abs_sum a p
  have hb := qmaFourAxisWeights_abs_sum b q
  have ha0 : 0 ≤ ∑ k, |qmaFourAxisWeights a p k| := by positivity
  have hb0 : 0 ≤ ∑ k, |qmaFourAxisWeights b q k| := by positivity
  nlinarith

theorem qmaFourTensorCoupling_norm (i j : Fin n) (a b : Fin 2) (t : ℝ) :
    ‖spinMatrixOperator (qmaFourTensorCoupling i j a b t)‖ ≤ 7056*(1+|t|) := by
  rw [qmaFourTensorCoupling,spinMatrixOperator_smul,norm_smul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (qmaFourCouplingSize_nonneg a b t)]
  have hn := qmaFourTensorAxisCross_norm i j a b true (qmaFourCouplingSign t)
  have hs := qmaFourCouplingSize_bound a b t
  have hnon := qmaFourCouplingSize_nonneg a b t
  calc
    _ ≤ qmaFourCouplingSize a b t*2352 := mul_le_mul_of_nonneg_left hn hnon
    _ ≤ _ := by nlinarith

end ContinuumCoulomb

end

end OAI
