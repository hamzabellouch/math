import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFourAxis
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumEightBasis

namespace OAI

/-! Dimension-independent operator bounds for the actual exchange encoding. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaFourSpin_norm (i : Fin 4) (μ : Fin 3) : ‖spinMatrixOperator (qmaFourSpin i μ)‖ ≤ 1 := by
  rw [qmaFourSpin_source]
  change ‖spinMatrixOperator ((sourceLocalPauli 4 i μ).submatrix
    qmaFourBasisEquiv.symm qmaFourBasisEquiv.symm)‖ ≤ 1
  rw [MediatorGraph.reindex_operator_norm]
  exact sourceLocalPauli_operator_norm 4 i μ

theorem qmaFourExchange_norm (i j : Fin 4) (hij : i ≠ j) :
    ‖spinMatrixOperator (qmaFourExchange i j)‖ ≤ 3 := by
  rw [qmaFourExchange_source]
  change ‖spinMatrixOperator ((sourceHeisenbergMatrix 4 i j).submatrix
    qmaFourBasisEquiv.symm qmaFourBasisEquiv.symm)‖ ≤ 3
  rw [MediatorGraph.reindex_operator_norm]
  exact sourceHeisenbergMatrix_operator_norm 4 i j hij

theorem qmaFourCross_norm (i j : Fin 4) : ‖spinMatrixOperator (qmaFourCross i j)‖ ≤ 3 := by
  rw [← qmaFourCross_source,MediatorGraph.reindex_operator_norm]
  apply sourceHeisenbergMatrix_operator_norm
  intro h
  have hv := congrArg Fin.val h
  have hi := i.isLt
  simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
  omega

theorem qmaFourWeightedCross_norm (a b : Fin 4 → ℝ) :
    ‖spinMatrixOperator (qmaFourWeightedCross a b)‖ ≤
      3*(∑ i, |a i|)*(∑ j, |b j|) := by
  rw [qmaFourWeightedCross,spinMatrixOperator_sum]
  calc
    _ ≤ ∑ i, ∑ j, 3*|a i| *|b j| := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro i _
      rw [spinMatrixOperator_sum]
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro j _
      rw [spinMatrixOperator_smul,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_mul]
      calc
        _ ≤ (|a i| *|b j|)*3 := mul_le_mul_of_nonneg_left (qmaFourCross_norm i j) (by positivity)
        _ = _ := by ring
    _ = (∑ i, 3*|a i|)*(∑ j, |b j|) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
    _ = _ := by rw [← Finset.mul_sum]

theorem qmaFourAxisWeights_abs_sum (a : Fin 2) (p : Bool) :
    (∑ i, |qmaFourAxisWeights a p i|) ≤ 28 := by
  fin_cases a <;> cases p <;>
    norm_num [qmaFourAxisWeights,qmaFourXWeights,qmaFourZWeights,Fin.sum_univ_succ]

theorem qmaFourAxisCross_norm (a b : Fin 2) (p q : Bool) :
    ‖spinMatrixOperator (qmaFourWeightedCross (qmaFourAxisWeights a p) (qmaFourAxisWeights b q))‖ ≤
      2352 := by
  apply (qmaFourWeightedCross_norm _ _).trans
  have ha := qmaFourAxisWeights_abs_sum a p
  have hb := qmaFourAxisWeights_abs_sum b q
  have ha0 : 0 ≤ ∑ i, |qmaFourAxisWeights a p i| := by positivity
  have hb0 : 0 ≤ ∑ i, |qmaFourAxisWeights b q i| := by positivity
  nlinarith

end ContinuumCoulomb

end

end OAI
