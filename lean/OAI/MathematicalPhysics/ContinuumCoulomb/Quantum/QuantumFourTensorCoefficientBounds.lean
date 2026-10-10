import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFourTensorFields

namespace OAI

/-! Polynomial bounds for the internal counterterm coefficients. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaFourCouplingFactor_nonneg (a b : Fin 2) (t : ℝ) : 0 ≤ qmaFourCouplingFactor a b t := by
  unfold qmaFourCouplingFactor
  positivity

theorem qmaFourCouplingFactor_bound (a b : Fin 2) (t : ℝ) : qmaFourCouplingFactor a b t ≤ |t| := by
  have ha := (qmaFourAxisScale_bounds a).1
  have hb := (qmaFourAxisScale_bounds b).1
  have hf := qmaFourCouplingFactor_nonneg a b t
  have he : qmaFourCouplingFactor a b t*qmaFourAxisScale a*qmaFourAxisScale b = |t| :=
    qmaFourCouplingSize_square a b t
  calc
    _ ≤ qmaFourCouplingFactor a b t*qmaFourAxisScale a := by nlinarith
    _ ≤ qmaFourCouplingFactor a b t*qmaFourAxisScale a*qmaFourAxisScale b := by
      exact le_mul_of_one_le_right (mul_nonneg hf (le_trans (by norm_num) ha)) hb
    _ = _ := he

theorem qmaFourAxisShift_abs_bound (a : Fin 2) (p : Bool) : |qmaFourAxisShift a p| ≤ 400 := by
  fin_cases a <;> cases p <;> norm_num [qmaFourAxisShift]

theorem qmaFourAxisScale_abs_bound (a : Fin 2) : |qmaFourAxisScale a| ≤ 256 := by
  rw [abs_of_pos (qmaFourAxisScale_pos a)]
  exact (qmaFourAxisScale_bounds a).2

theorem qmaFourAxisSign_abs (p : Bool) : |qmaFourAxisSign p| = 1 := by
  cases p <;> norm_num [qmaFourAxisSign]

theorem qmaFourCounterA_bound (a b : Fin 2) (t : ℝ) : |qmaFourCounterA a b t| ≤ 102400*|t| := by
  rw [qmaFourCounterA,abs_mul,abs_mul,abs_of_nonneg (qmaFourCouplingFactor_nonneg a b t)]
  calc
    _ ≤ (|t| * 256)*400 := mul_le_mul
      (mul_le_mul (qmaFourCouplingFactor_bound a b t) (qmaFourAxisScale_abs_bound a)
        (abs_nonneg _) (abs_nonneg t)) (qmaFourAxisShift_abs_bound b _)
      (abs_nonneg _) (by positivity)
    _ = _ := by ring

theorem qmaFourCounterB_bound (a b : Fin 2) (t : ℝ) : |qmaFourCounterB a b t| ≤ 102400*|t| := by
  rw [qmaFourCounterB,abs_mul,abs_mul,abs_mul,qmaFourAxisSign_abs,one_mul,
    abs_of_nonneg (qmaFourCouplingFactor_nonneg a b t)]
  calc
    _ ≤ (|t| * 400)*256 := mul_le_mul
      (mul_le_mul (qmaFourCouplingFactor_bound a b t) (qmaFourAxisShift_abs_bound a true)
        (abs_nonneg _) (abs_nonneg t)) (qmaFourAxisScale_abs_bound b)
      (abs_nonneg _) (by positivity)
    _ = _ := by ring

variable {n : ℕ} {κ : Type*} [Fintype κ]

theorem qmaFourTensorCounterterm_linear_bound (i j : Fin n) (a b : Fin 2) (t : ℝ) :
    ‖spinMatrixOperator (qmaFourTensorCounterterm i j a b t)‖ ≤ 1228800*|t| := by
  apply (qmaFourTensorCounterterm_norm i j a b t).trans
  have ha := qmaFourCounterA_bound a b t
  have hb := qmaFourCounterB_bound a b t
  linarith

theorem qmaFourTensorFamilyCounterterm_bound (left right : κ → Fin n)
    (a b : κ → Fin 2) (t : κ → ℝ) :
    ‖spinMatrixOperator (qmaFourTensorFamilyCounterterm left right a b t)‖ ≤
      1228800*(∑ e, |t e|) := by
  rw [qmaFourTensorFamilyCounterterm,spinMatrixOperator_sum,Finset.mul_sum]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun e _ => qmaFourTensorCounterterm_linear_bound _ _ _ _ _))

theorem qmaFourTensorFamilyCounterterm_star (left right : κ → Fin n)
    (a b : κ → Fin 2) (t : κ → ℝ) :
    (qmaFourTensorFamilyCounterterm left right a b t).conjTranspose =
      qmaFourTensorFamilyCounterterm left right a b t := by
  simp only [qmaFourTensorFamilyCounterterm,Matrix.conjTranspose_sum,qmaFourTensorCounterterm_star]

end ContinuumCoulomb

end

end OAI
