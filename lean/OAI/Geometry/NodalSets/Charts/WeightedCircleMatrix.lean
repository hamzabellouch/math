import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

namespace Yau.Geometry
open Matrix
noncomputable section
variable {n : Type*} [Fintype n] [DecidableEq n]

def circleWeight (h : Matrix n n ℝ) (rho gamma0 : ℝ) : ℝ :=
  rho*gamma0 / Real.sqrt h.det

def weightedCircleMatrix (h : Matrix n n ℝ) (rho gamma0 : ℝ) :
    Matrix (n ⊕ Fin 1) (n ⊕ Fin 1) ℝ :=
  Matrix.fromBlocks h 0 0 (Matrix.of fun _ _ ↦ (circleWeight h rho gamma0)^2)

lemma circleWeight_pos {h : Matrix n n ℝ} (hh : h.PosDef) {rho gamma0 : ℝ}
    (hr : 0 < rho) (hg : 0 < gamma0) : 0 < circleWeight h rho gamma0 :=
  div_pos (mul_pos hr hg) (Real.sqrt_pos.mpr hh.det_pos)

lemma weightedCircleMatrix_det {h : Matrix n n ℝ} (hh : h.PosDef) (rho gamma0 : ℝ) :
    (weightedCircleMatrix h rho gamma0).det = (rho*gamma0)^2 := by
  rw [weightedCircleMatrix,det_fromBlocks_zero₂₁,det_fin_one]
  dsimp [circleWeight]
  rw [div_pow,Real.sq_sqrt hh.det_pos.le]
  field_simp [hh.det_pos.ne']

lemma weightedCircleMatrix_volume {h : Matrix n n ℝ} (hh : h.PosDef) {rho gamma0 : ℝ}
    (hr : 0 < rho) (hg : 0 < gamma0) :
    Real.sqrt (weightedCircleMatrix h rho gamma0).det = rho*gamma0 := by
  rw [weightedCircleMatrix_det hh,Real.sqrt_sq (mul_pos hr hg).le]

lemma weightedCircleMatrix_horizontal_inverse {h : Matrix n n ℝ} (hh : h.PosDef)
    {rho gamma0 : ℝ} (hr : 0 < rho) (hg : 0 < gamma0) (i j : n) :
    (weightedCircleMatrix h rho gamma0)⁻¹ (Sum.inl i) (Sum.inl j) = h⁻¹ i j := by
  have hD : IsUnit (Matrix.of (fun _ _ : Fin 1 ↦ (circleWeight h rho gamma0)^2)) := by
    rw [Matrix.isUnit_iff_isUnit_det,det_fin_one]
    exact isUnit_iff_ne_zero.mpr (pow_ne_zero _ (circleWeight_pos hh hr hg).ne')
  unfold weightedCircleMatrix
  rw [inv_fromBlocks_zero₂₁_of_isUnit_iff h 0 _ (iff_of_true hh.isUnit hD)]
  rfl

lemma weightedCircleMatrix_posDef {h : Matrix n n ℝ} (hh : h.PosDef)
    {rho gamma0 : ℝ} (hr : 0 < rho) (hg : 0 < gamma0) :
    (weightedCircleMatrix h rho gamma0).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · apply Matrix.IsHermitian.fromBlocks hh.1
    · simp
    · exact Matrix.isHermitian_iff_isSymm.mpr (by ext i j; rfl)
  · intro x hx
    have hq := circleWeight_pos hh hr hg
    have heq : star x ⬝ᵥ ((weightedCircleMatrix h rho gamma0) *ᵥ x) =
        star (fun i ↦ x (Sum.inl i)) ⬝ᵥ (h *ᵥ (fun i ↦ x (Sum.inl i))) +
          (circleWeight h rho gamma0)^2 * (x (Sum.inr 0))^2 := by
      simp [weightedCircleMatrix,Matrix.fromBlocks,dotProduct,mulVec,Fintype.sum_sum_type]
      ring
    rw [heq]
    by_cases hleft : (fun i ↦ x (Sum.inl i)) = 0
    · have hright : x (Sum.inr 0) ≠ 0 := by
        intro hz
        apply hx
        funext i
        cases i with
        | inl i => exact congrFun hleft i
        | inr i => simpa [Subsingleton.elim i 0] using hz
      simp only [hleft,mulVec_zero,dotProduct_zero,zero_add]
      exact mul_pos (sq_pos_of_pos hq) (sq_pos_of_ne_zero hright)
    · exact add_pos_of_pos_of_nonneg (hh.dotProduct_mulVec_pos hleft) (by positivity)

end
end Yau.Geometry

end OAI
