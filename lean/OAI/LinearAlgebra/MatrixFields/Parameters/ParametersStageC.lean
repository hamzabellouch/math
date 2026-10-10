import Mathlib
import OAI.LinearAlgebra.MatrixFields.Histories.HistoryChildLaws

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

namespace MatrixMultiplication.AllFieldParameters

open scoped BigOperators

noncomputable section

theorem stageC_direct_identity {I : Type*} [Fintype I]
    (mass entropy : I → ℝ) (allocation logTwo : ℝ) :
    (∑ i, mass i * ((1 - allocation) * logTwo + allocation * entropy i)) =
      (∑ i, mass i) * logTwo - 3 * allocation *
        ((∑ i, mass i) * logTwo -
          (∑ i, mass i * (2 * logTwo + entropy i)) / 3) := by
  calc
    _ = (∑ i, mass i * logTwo) - 3 * allocation *
        ((∑ i, mass i * logTwo) -
          (∑ i, mass i * (2 * logTwo + entropy i)) / 3) := by
      rw [Finset.sum_div, ← Finset.sum_sub_distrib, Finset.mul_sum,
        ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [Finset.sum_mul]

theorem stageC_direct_balanced {I : Type*} [Fintype I]
    (mass entropy : I → ℝ) (a b : Staggering.Capacity) (i : Fin 3)
    (hgap :
      (∑ j, mass j * (2 * Real.log 2 + entropy j)) / 3 <
        (∑ j, mass j) * Real.log 2) :
    let high := (∑ j, mass j) * Real.log 2
    let base := (∑ j, mass j * (2 * Real.log 2 + entropy j)) / 3
    let allocation := Staggering.balanceFraction a b high base i
    (∑ j, mass j * ((1 - allocation) * Real.log 2 + allocation * entropy j)) =
      Staggering.totalCapacity a b base - (a i + b i) := by
  dsimp only
  rw [stageC_direct_identity]
  exact Staggering.thirdCapacity_eq a b _ _ hgap i

end

end MatrixMultiplication.AllFieldParameters

end MatrixAllFields

end OAI
