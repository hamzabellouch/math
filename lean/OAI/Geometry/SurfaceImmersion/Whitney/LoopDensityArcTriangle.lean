import OAI.Geometry.SurfaceImmersion.Primitive.LoopDensityBumpSelection

namespace OAI

/-! A nondegenerate three-point barycenter inside a symmetric circular arc. -/
noncomputable section
open scoped Matrix BigOperators

namespace ClosedSurfaceR4.LoopDensity

def arcTriangle (q s : ℝ) : Fin 3 → Plane := ![![1, 0], ![q, s], ![q, -s]]

def arcWeights (q m : ℝ) : Moments :=
  ![(m - q) / (1 - q), (1 - m) / (2 * (1 - q)), (1 - m) / (2 * (1 - q))]

lemma arcWeights_pos {q m : ℝ} (hqm : q < m) (hm : m < 1) (i : Fin 3) :
    0 < arcWeights q m i := by
  have hq : 0 < 1 - q := by linarith
  have hnum : 0 < m - q := sub_pos.mpr hqm
  have hm' : 0 < 1 - m := sub_pos.mpr hm
  fin_cases i
  · exact div_pos hnum hq
  · exact div_pos hm' (mul_pos (by norm_num) hq)
  · exact div_pos hm' (mul_pos (by norm_num) hq)

lemma arcTriangle_barycenter {q m : ℝ} (hq : q ≠ 1) (s : ℝ) :
    columnOperator (fun i => augment (arcTriangle q s i)) (arcWeights q m) = augment ![m, 0] := by
  have hd : 1 - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
  ext i
  fin_cases i <;> simp [columnOperator, arcTriangle, arcWeights, augment, Fin.sum_univ_three] <;>
    field_simp [hd] <;> ring

lemma arcTriangle_invertible {q s : ℝ} (hq : q ≠ 1) (hs : s ≠ 0) :
    (columnOperator (fun i => augment (arcTriangle q s i))).IsInvertible := by
  let M : Matrix (Fin 3) (Fin 3) ℝ :=
    Matrix.of (fun i j => augment (arcTriangle q s j) i)
  have hdet : M.det = 2 * s * (1 - q) := by
    rw [Matrix.det_fin_three M]
    norm_num [M, arcTriangle, augment]
    ring
  have hd : M.det ≠ 0 := by
    rw [hdet]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hs) (sub_ne_zero.mpr (Ne.symm hq))
  have hunit : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).mpr (isUnit_iff_ne_zero.mpr hd)
  have heval (x : Moments) : M.mulVec x = columnOperator (fun i => augment (arcTriangle q s i)) x := by
    ext i
    simp [M, Matrix.mulVec, dotProduct, columnOperator, mul_comm]
  have hi : Function.Injective (columnOperator (fun i => augment (arcTriangle q s i))) := by
    intro x y h
    apply (Matrix.mulVec_injective_iff_isUnit.mpr hunit)
    simpa only [heval] using h
  have hsurj := LinearMap.surjective_of_injective
    (f := (columnOperator (fun i => augment (arcTriangle q s i))).toLinearMap) hi
  exact ⟨(LinearEquiv.ofBijective _ ⟨hi, hsurj⟩).toContinuousLinearEquiv, rfl⟩

end ClosedSurfaceR4.LoopDensity

end

end OAI
