import OAI.Analysis.LipschitzHilbert.Estimates.PublishedInputs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace OAI

/-! The orthonormal long and transverse axes of an actual slope box. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

def slopeAxisVectors (s : ℝ) : Fin 2 → Plane :=
  ![WithLp.toLp 2 ![1/Real.sqrt (1+s^2), s/Real.sqrt (1+s^2)],
    WithLp.toLp 2 ![-s/Real.sqrt (1+s^2), 1/Real.sqrt (1+s^2)]]

theorem slopeAxisVectors_orthonormal (s : ℝ) : Orthonormal ℝ (slopeAxisVectors s) := by
  have hpos : 0 < 1+s^2 := by positivity
  have hq : Real.sqrt (1+s^2) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  have hq2 := Real.sq_sqrt hpos.le
  rw [orthonormal_iff_ite]
  intro i j
  change (∑ k, slopeAxisVectors s j k * slopeAxisVectors s i k) = _
  fin_cases i <;> fin_cases j <;>
    simp [slopeAxisVectors, Fin.sum_univ_two] <;>
    field_simp [hq] <;> nlinarith

def slopeAxes (s : ℝ) : OrthonormalBasis (Fin 2) ℝ Plane :=
  OrthonormalBasis.mk (slopeAxisVectors_orthonormal s)
    ((slopeAxisVectors_orthonormal s).linearIndependent.span_eq_top_of_card_eq_finrank'
      (by simp [Plane])).ge

theorem slopeAxes_apply (s : ℝ) (i : Fin 2) : slopeAxes s i = slopeAxisVectors s i := by
  exact congrFun (OrthonormalBasis.coe_mk _ _) i

theorem slopeAxes_repr_zero (s : ℝ) (z : Plane) :
    (slopeAxes s).repr z 0 = (z 0+s*z 1)/Real.sqrt (1+s^2) := by
  rw [OrthonormalBasis.repr_apply_apply, slopeAxes_apply]
  simp [slopeAxisVectors, PiLp.inner_apply, Fin.sum_univ_two]
  ring

theorem slopeAxes_repr_one (s : ℝ) (z : Plane) :
    (slopeAxes s).repr z 1 = (z 1-s*z 0)/Real.sqrt (1+s^2) := by
  rw [OrthonormalBasis.repr_apply_apply, slopeAxes_apply]
  simp [slopeAxisVectors, PiLp.inner_apply, Fin.sum_univ_two]
  ring

end LipschitzHilbert

end

end OAI
