import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFourNorm
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFourEffective

namespace OAI

/-! Polynomial bounds for the physically calibrated inter-block interaction. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaFourAxisScale_bounds (a : Fin 2) : 1 ≤ qmaFourAxisScale a ∧ qmaFourAxisScale a ≤ 256 := by
  have hs0 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
  have hs2 : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  fin_cases a
  · norm_num [qmaFourAxisScale]
    constructor <;> nlinarith
  · norm_num [qmaFourAxisScale]

theorem qmaFourCouplingSize_bound (a b : Fin 2) (j : ℝ) :
    qmaFourCouplingSize a b j ≤ 3*(1+|j|) := by
  have ha := (qmaFourAxisScale_bounds a).1
  have hb := (qmaFourAxisScale_bounds b).1
  have hp : 1 ≤ qmaFourAxisScale a*qmaFourAxisScale b := by nlinarith
  have hr := qmaFourCouplingSize_nonneg a b j
  have he := qmaFourCouplingSize_square a b j
  have hm := mul_le_mul_of_nonneg_left hp (sq_nonneg (qmaFourCouplingSize a b j))
  have hsq : (qmaFourCouplingSize a b j)^2 ≤ (8/3)*|j| := by nlinarith
  have hj := abs_nonneg j
  nlinarith [sq_nonneg |j|]

theorem qmaFourCoupling_norm (a b : Fin 2) (j : ℝ) :
    ‖spinMatrixOperator (qmaFourCoupling a b j)‖ ≤ 7056*(1+|j|) := by
  rw [qmaFourCoupling,spinMatrixOperator_smul,norm_smul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (qmaFourCouplingSize_nonneg a b j)]
  have hn := qmaFourAxisCross_norm a b true (qmaFourCouplingSign j)
  have hs := qmaFourCouplingSize_bound a b j
  have hnon := qmaFourCouplingSize_nonneg a b j
  calc
    _ ≤ qmaFourCouplingSize a b j*2352 := mul_le_mul_of_nonneg_left hn hnon
    _ ≤ _ := by nlinarith

end ContinuumCoulomb

end

end OAI
