import OAI.Geometry.SurfaceImmersion.Primitive.LoopDensityBumpSelection

namespace OAI

/-! Three circle directions strictly surrounding any radial target in the open disk. -/
noncomputable section
open scoped Matrix BigOperators

namespace ClosedSurfaceR4.LoopDensity

def triangle (e : Plane) : Fin 3 → Plane :=
  ![e, ![-e 0 / 2 - Real.sqrt 3 / 2 * e 1, -e 1 / 2 + Real.sqrt 3 / 2 * e 0],
    ![-e 0 / 2 + Real.sqrt 3 / 2 * e 1, -e 1 / 2 - Real.sqrt 3 / 2 * e 0]]

def triangleWeights (r : ℝ) : Moments := ![(1 + 2 * r) / 3, (1 - r) / 3, (1 - r) / 3]

lemma triangleWeights_pos {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (i : Fin 3) :
    0 < triangleWeights r i := by
  fin_cases i <;> simp [triangleWeights] <;> linarith

lemma triangle_barycenter (e : Plane) (r : ℝ) :
    columnOperator (fun i => augment (triangle e i)) (triangleWeights r) = augment (r • e) := by
  ext i
  fin_cases i <;>
    simp [columnOperator, triangle, triangleWeights, augment, Fin.sum_univ_three] <;> ring

lemma triangle_determinant {e : Plane} (he : e 0 ^ 2 + e 1 ^ 2 = 1) :
    Matrix.det (Matrix.of (fun i j : Fin 3 => augment (triangle e j) i)) = 3 * Real.sqrt 3 / 2 := by
  calc
    _ = (3 * Real.sqrt 3 / 2) * (e 0 ^ 2 + e 1 ^ 2) := by
      rw [Matrix.det_fin_three (Matrix.of (fun i j : Fin 3 => augment (triangle e j) i))]
      norm_num [triangle, augment]
      ring
    _ = _ := by rw [he, mul_one]

lemma triangle_invertible {e : Plane} (he : e 0 ^ 2 + e 1 ^ 2 = 1) :
    (columnOperator (fun i => augment (triangle e i))).IsInvertible := by
  let M : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of (fun i j => augment (triangle e j) i)
  have hd : IsUnit M.det := by
    rw [triangle_determinant he]
    exact isUnit_iff_ne_zero.mpr (by positivity)
  have hm : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).mpr hd
  have heval (x : Moments) : M.mulVec x = columnOperator (fun i => augment (triangle e i)) x := by
    ext i
    simp [M, Matrix.mulVec, dotProduct, columnOperator, mul_comm]
  have hi : Function.Injective (columnOperator (fun i => augment (triangle e i))) := by
    intro x y h
    apply (Matrix.mulVec_injective_iff_isUnit.mpr hm)
    simpa only [heval] using h
  have hs := LinearMap.surjective_of_injective
    (f := (columnOperator (fun i => augment (triangle e i))).toLinearMap) hi
  exact ⟨(LinearEquiv.ofBijective _ ⟨hi, hs⟩).toContinuousLinearEquiv, rfl⟩

lemma triangle_unit {e : Plane} (he : e 0 ^ 2 + e 1 ^ 2 = 1) (i : Fin 3) :
    (triangle e i) 0 ^ 2 + (triangle e i) 1 ^ 2 = 1 := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  fin_cases i
  · exact he
  · change (-e 0 / 2 - Real.sqrt 3 / 2 * e 1) ^ 2 +
      (-e 1 / 2 + Real.sqrt 3 / 2 * e 0) ^ 2 = 1
    ring_nf
    rw [hs]
    nlinarith [he]
  · change (-e 0 / 2 + Real.sqrt 3 / 2 * e 1) ^ 2 +
      (-e 1 / 2 - Real.sqrt 3 / 2 * e 0) ^ 2 = 1
    ring_nf
    rw [hs]
    nlinarith [he]

end ClosedSurfaceR4.LoopDensity

end

end OAI
