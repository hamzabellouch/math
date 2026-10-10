import OAI.Geometry.EinsteinFour.QuaternionLifts

namespace OAI

/-! The rotation of the matrix indices is recovered from the actual
quaternion commutator.  Thus a four-dimensional quaternion lift also
intertwines the three-dimensional infinitesimal rotation generators. -/

namespace PositiveEinsteinFour.QuaternionFrame

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry

noncomputable section

theorem imaginaryCombination_apply (Q : Fin 3 → Mat4) (u : Fin 3 → ℝ)
    (i j : Fin 4) : imaginaryCombination Q u i j = ∑ r, u r * Q r i j := by
  change (∑ r, u r • Q r) i j = _
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

theorem imaginaryLeft_entry (u : Fin 3 → ℝ) (r : Fin 3) :
    imaginaryCombination quaternionMatrix u r.succ 0 = u r := by
  rw [imaginaryCombination_apply]
  fin_cases r <;> norm_num [quaternionMatrix, Fin.sum_univ_three]

theorem imaginaryLeft_injective :
    Function.Injective (imaginaryCombination quaternionMatrix) := by
  intro u v huv
  funext r
  simpa only [imaginaryLeft_entry] using
    congrArg (fun M : Mat4 => M r.succ 0) huv

private theorem imaginaryLeft_commutator_0 (v : Fin 3 → ℝ) :
    quaternionMatrix 0 * imaginaryCombination quaternionMatrix v -
      imaginaryCombination quaternionMatrix v * quaternionMatrix 0 =
        imaginaryCombination quaternionMatrix (TraceHessian.rotation 0 *ᵥ v) := by
  ext i j
  simp only [Matrix.sub_apply, Matrix.mul_apply, imaginaryCombination_apply,
    Matrix.mulVec, dotProduct]
  fin_cases i <;> fin_cases j <;>
    norm_num [quaternionMatrix, TraceHessian.rotation, Fin.sum_univ_three,
      Fin.sum_univ_four] <;> ring

private theorem imaginaryLeft_commutator_1 (v : Fin 3 → ℝ) :
    quaternionMatrix 1 * imaginaryCombination quaternionMatrix v -
      imaginaryCombination quaternionMatrix v * quaternionMatrix 1 =
        imaginaryCombination quaternionMatrix (TraceHessian.rotation 1 *ᵥ v) := by
  ext i j
  simp only [Matrix.sub_apply, Matrix.mul_apply, imaginaryCombination_apply,
    Matrix.mulVec, dotProduct]
  fin_cases i <;> fin_cases j <;>
    norm_num [quaternionMatrix, TraceHessian.rotation, Fin.sum_univ_three,
      Fin.sum_univ_four] <;> ring

private theorem imaginaryLeft_commutator_2 (v : Fin 3 → ℝ) :
    quaternionMatrix 2 * imaginaryCombination quaternionMatrix v -
      imaginaryCombination quaternionMatrix v * quaternionMatrix 2 =
        imaginaryCombination quaternionMatrix (TraceHessian.rotation 2 *ᵥ v) := by
  ext i j
  simp only [Matrix.sub_apply, Matrix.mul_apply, imaginaryCombination_apply,
    Matrix.mulVec, dotProduct]
  fin_cases i <;> fin_cases j <;>
    norm_num [quaternionMatrix, TraceHessian.rotation, Fin.sum_univ_three,
      Fin.sum_univ_four] <;> ring

/-- The speed-two generator in the matrix indices is the commutator
of the corresponding unit imaginary quaternion. -/
theorem imaginaryLeft_commutator (s : Fin 3) (v : Fin 3 → ℝ) :
    quaternionMatrix s * imaginaryCombination quaternionMatrix v -
      imaginaryCombination quaternionMatrix v * quaternionMatrix s =
        imaginaryCombination quaternionMatrix (TraceHessian.rotation s *ᵥ v) := by
  fin_cases s
  · exact imaginaryLeft_commutator_0 v
  · exact imaginaryLeft_commutator_1 v
  · exact imaginaryLeft_commutator_2 v

theorem imaginaryLeft_general_commutator (u v : Fin 3 → ℝ) :
    imaginaryCombination quaternionMatrix u * imaginaryCombination quaternionMatrix v -
      imaginaryCombination quaternionMatrix v * imaginaryCombination quaternionMatrix u =
        imaginaryCombination quaternionMatrix
          ((∑ r, u r • TraceHessian.rotation r) *ᵥ v) := by
  calc
    _ = ∑ r, u r • (quaternionMatrix r * imaginaryCombination quaternionMatrix v -
          imaginaryCombination quaternionMatrix v * quaternionMatrix r) := by
      have hlinear (V : Mat4) :
          (∑ r, u r • quaternionMatrix r) * V - V * (∑ r, u r • quaternionMatrix r) =
            ∑ r, u r • (quaternionMatrix r * V - V * quaternionMatrix r) := by
        simp only [Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul,
          Matrix.mul_smul, smul_sub, Finset.sum_sub_distrib]
      exact hlinear _
    _ = ∑ r, u r • imaginaryCombination quaternionMatrix
        (TraceHessian.rotation r *ᵥ v) := by simp_rw [imaginaryLeft_commutator]
    _ = _ := by
      simp only [imaginaryCombination, Matrix.sum_mulVec, Matrix.smul_mulVec,
        Finset.sum_apply, Pi.smul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
      change (∑ r, ∑ s, (u r * (TraceHessian.rotation r *ᵥ v) s) • quaternionMatrix s) =
        ∑ s, ∑ r, (u r * (TraceHessian.rotation r *ᵥ v) s) • quaternionMatrix s
      exact Finset.sum_comm

theorem QuaternionLift.mul_transpose {R : Mat}
    (P : QuaternionLift quaternionMatrix Angular.oppositeMatrix R) :
    P.matrix * P.matrixᵀ = 1 :=
  mul_eq_one_comm.mp P.orthogonal

/-- The matrix rotation generators transform under exactly the same
three-dimensional frame change as the imaginary quaternion basis. -/
theorem QuaternionLift.rotation_intertwines {R : Mat}
    (P : QuaternionLift quaternionMatrix Angular.oppositeMatrix R) (s : Fin 3) :
    R * TraceHessian.rotation s =
      (∑ r, R r s • TraceHessian.rotation r) * R := by
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  apply imaginaryLeft_injective
  have hc := imaginaryLeft_general_commutator (fun r => R r s) (R *ᵥ v)
  have hl := imaginaryLeft_commutator s v
  have hv := intertwines_combination quaternionMatrix R P.matrix P.intertwines v
  have hw := intertwines_combination quaternionMatrix R P.matrix P.intertwines
    (TraceHessian.rotation s *ᵥ v)
  have hp := P.intertwines s
  have he : imaginaryCombination quaternionMatrix (R *ᵥ (TraceHessian.rotation s *ᵥ v)) *
      P.matrix =
      imaginaryCombination quaternionMatrix
        ((∑ r, R r s • TraceHessian.rotation r) *ᵥ (R *ᵥ v)) * P.matrix := by
    rw [← hw, ← hl, ← hc]
    change P.matrix * (quaternionMatrix s * imaginaryCombination quaternionMatrix v -
      imaginaryCombination quaternionMatrix v * quaternionMatrix s) =
      ((∑ r, R r s • quaternionMatrix r) *
        imaginaryCombination quaternionMatrix (R *ᵥ v) -
        imaginaryCombination quaternionMatrix (R *ᵥ v) *
          (∑ r, R r s • quaternionMatrix r)) * P.matrix
    rw [Matrix.mul_sub, Matrix.sub_mul]
    congr 1
    · rw [← Matrix.mul_assoc, hp, Matrix.mul_assoc, hv, ← Matrix.mul_assoc]
    · rw [← Matrix.mul_assoc, hv, Matrix.mul_assoc, hp, ← Matrix.mul_assoc]
  have he' := congrArg (fun M : Mat4 => M * P.matrixᵀ) he
  simpa only [Matrix.mul_assoc, P.mul_transpose, Matrix.mul_one,
    Matrix.mulVec_mulVec] using he'

end
end PositiveEinsteinFour.QuaternionFrame

end OAI
