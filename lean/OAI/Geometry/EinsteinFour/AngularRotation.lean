import OAI.Geometry.EinsteinFour.AngularQuadratic

namespace OAI

/-! The actual change of normal bases `I_s q` and `J_t q`. Its spherical
orthogonality is a consequence of the fourth monomial moment. -/

namespace PositiveEinsteinFour.Angular

open Matrix

noncomputable section

def oppositeMatrix (s : Fin 3) : Mat4 := Geometry.oppositeQuaternion s

def mixingCoefficient (r s : Fin 3) : Mat4 :=
  (TraceHessian.quaternionMatrix r)ᵀ * oppositeMatrix s

def coefficientTable (r s : Fin 3) : Mat4 :=
  ![![![![-1, 0, 0, 0], ![0, -1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]], ![![0, 0, 0, 1], ![0, 0, -1, 0], ![0, -1, 0, 0], ![1, 0, 0, 0]], ![![0, 0, -1, 0], ![0, 0, 0, -1], ![-1, 0, 0, 0], ![0, -1, 0, 0]]], ![![![0, 0, 0, -1], ![0, 0, -1, 0], ![0, -1, 0, 0], ![-1, 0, 0, 0]], ![![-1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, -1, 0], ![0, 0, 0, 1]], ![![0, 1, 0, 0], ![1, 0, 0, 0], ![0, 0, 0, -1], ![0, 0, -1, 0]]], ![![![0, 0, 1, 0], ![0, 0, 0, -1], ![1, 0, 0, 0], ![0, -1, 0, 0]], ![![0, -1, 0, 0], ![-1, 0, 0, 0], ![0, 0, 0, -1], ![0, 0, -1, 0]], ![![-1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, -1]]]] r s

theorem mixingCoefficient_eq_table (r s : Fin 3) :
    mixingCoefficient r s = coefficientTable r s := by
  ext i j
  simp only [mixingCoefficient, Matrix.mul_apply, Matrix.transpose_apply]
  fin_cases r <;> fin_cases s <;> fin_cases i <;> fin_cases j <;>
    norm_num [TraceHessian.quaternionMatrix, oppositeMatrix,
      Geometry.oppositeQuaternion, coefficientTable, Fin.sum_univ_succ]

def mixing (r s : Fin 3) (q : Directions) : ℝ :=
  quadratic (mixingCoefficient r s) q

def mixingMatrix (q : Directions) : Geometry.Mat3 := fun r s => mixing r s q

theorem mixingCoefficient_symmetric (r s : Fin 3) :
    (mixingCoefficient r s)ᵀ = mixingCoefficient r s := by
  rw [mixingCoefficient_eq_table]
  ext i j
  change coefficientTable r s j i = coefficientTable r s i j
  fin_cases r <;> fin_cases s <;> fin_cases i <;> fin_cases j <;>
    norm_num [coefficientTable]

theorem mixingCoefficient_trace (r s : Fin 3) :
    (mixingCoefficient r s).trace = 0 := by
  rw [mixingCoefficient_eq_table]
  fin_cases r <;> fin_cases s <;>
    norm_num [coefficientTable, Matrix.trace, Matrix.diag, Fin.sum_univ_succ]

theorem mixingCoefficient_pairing (r s t u : Fin 3) :
    (∑ i, ∑ j, mixingCoefficient r s i j * mixingCoefficient t u i j) =
      if r = t then (if s = u then (4 : ℝ) else 0) else 0 := by
  simp only [mixingCoefficient_eq_table]
  fin_cases r <;> fin_cases s <;> fin_cases t <;> fin_cases u <;>
    norm_num [coefficientTable, Fin.sum_univ_succ]

theorem integral_mixing_mul (h : FollandMoments) (r s t u : Fin 3) :
    (∫ q, mixing r s q * mixing t u q ∂sphereMeasure) =
      if r = t then (if s = u then (1 / 3 : ℝ) else 0) else 0 := by
  unfold mixing
  rw [integral_quadratic_mul_traceFree h _ _ (mixingCoefficient_trace r s)
    (mixingCoefficient_trace t u) (mixingCoefficient_symmetric t u),
    mixingCoefficient_pairing]
  split_ifs <;> norm_num

theorem direction_sum_sq (q : Directions) : (∑ i, q.val i ^ 2) = 1 := by
  have h := congrArg (fun x : ℝ => x ^ 2) q.property
  simpa only [EuclideanSpace.real_norm_sq_eq, one_pow] using h

/-- The two triples give orthonormal normal bases for every unit direction. -/
theorem mixing_orthogonal (q : Directions) :
    mixingMatrix q * (mixingMatrix q)ᵀ = 1 := by
  ext i j
  change (∑ s, mixing i s q * mixing j s q) = if i = j then 1 else 0
  calc
    _ = (∑ a, q.val a ^ 2) ^ 2 * (if i = j then 1 else 0) := by
      simp only [mixing, quadratic, mixingCoefficient_eq_table]
      fin_cases i <;> fin_cases j <;>
        simp [coefficientTable, Fin.sum_univ_succ]
      all_goals ring
    _ = _ := by rw [direction_sum_sq]; simp

end

end PositiveEinsteinFour.Angular

end OAI
