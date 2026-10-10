import OAI.GroupTheory.PolycyclicRecognition.Geometry.TriangularMatrixExponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace OAI

/-! # Invertibility of the averaged real triangular exponential

This is the linear operator appearing in the differential of exponential
coordinates. Its diagonal entries are integrals of positive real
exponentials, so they cannot vanish. No global exponential theorem is used.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Matrix.Norms.Operator
open MeasureTheory Set

variable {n : ℕ}

def triangularExpAverage (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  ∫ t in (0 : ℝ)..1, NormedSpace.exp (t • A)

theorem triangularExpAverage_mul (A : Matrix (Fin n) (Fin n) ℝ) :
    triangularExpAverage A * A = NormedSpace.exp A - 1 := by
  let R : Matrix (Fin n) (Fin n) ℝ →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
    (ContinuousLinearMap.mul ℝ (Matrix (Fin n) (Fin n) ℝ)).flip A
  have hc : Continuous (fun t : ℝ => NormedSpace.exp (t • A)) :=
    NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)
  have hm := R.intervalIntegral_comp_comm (a := 0) (b := 1) (hc.intervalIntegrable (μ := volume) 0 1)
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1) (fun t _ => hasDerivAt_exp_smul_const A t)
    ((hc.mul_const A).intervalIntegrable (μ := volume) 0 1)
  calc
    triangularExpAverage A * A = ∫ t in (0 : ℝ)..1, NormedSpace.exp (t • A) * A := hm.symm
    _ = NormedSpace.exp A - 1 := by
      rw [one_smul, zero_smul, NormedSpace.exp_zero] at hf
      exact hf

theorem triangularExpAverage_entry (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    triangularExpAverage A i j = ∫ t in (0 : ℝ)..1, NormedSpace.exp (t • A) i j := by
  let ev : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ :=
    { toFun := fun B => B i j
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  have hc : Continuous (fun t : ℝ => NormedSpace.exp (t • A)) :=
    NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)
  exact (ev.toContinuousLinearMap.intervalIntegral_comp_comm (hc.intervalIntegrable (μ := volume) 0 1)).symm

theorem triangularExpAverage_upper (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsUpperTriangular) : (triangularExpAverage A).IsUpperTriangular := by
  intro i j hji
  rw [triangularExpAverage_entry]
  have hzero (t : ℝ) : NormedSpace.exp (t • A) i j = 0 := by
    apply matrix_exp_upperTriangular (t • A) _ hji
    intro k l hlk
    simp only [Matrix.smul_apply, smul_eq_mul, hA hlk, mul_zero]
  simp only [hzero, intervalIntegral.integral_zero]

theorem triangularExpAverage_diagonal (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsUpperTriangular) (i : Fin n) :
    triangularExpAverage A i i = ∫ t in (0 : ℝ)..1, Real.exp (t * A i i) := by
  rw [triangularExpAverage_entry]
  apply intervalIntegral.integral_congr
  intro t _
  have ht : (t • A).IsUpperTriangular := by
    intro k l hlk
    simp only [Matrix.smul_apply, smul_eq_mul, hA hlk, mul_zero]
  change NormedSpace.exp (t • A) i i = Real.exp (t * A i i)
  rw [matrix_exp_diagonal (t • A) ht]
  rfl

theorem triangularExpAverage_diagonal_pos (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsUpperTriangular) (i : Fin n) : 0 < triangularExpAverage A i i := by
  rw [triangularExpAverage_diagonal A hA]
  apply intervalIntegral.integral_pos zero_lt_one
    (Real.continuous_exp.comp (continuous_id.mul_const (A i i))).continuousOn
  · intro t _
    exact (Real.exp_pos _).le
  · exact ⟨0, ⟨le_rfl, zero_le_one⟩, Real.exp_pos _⟩

theorem triangularExpAverage_isUnit (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsUpperTriangular) : IsUnit (triangularExpAverage A) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero,
    Matrix.det_of_isUpperTriangular (triangularExpAverage_upper A hA)]
  exact Finset.prod_ne_zero_iff.mpr fun i _ =>
    ne_of_gt (triangularExpAverage_diagonal_pos A hA i)

end PolycyclicRecognition

end

end OAI
