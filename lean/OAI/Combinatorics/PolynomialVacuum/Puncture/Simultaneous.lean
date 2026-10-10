import Mathlib

namespace OAI

namespace PolynomialVacuumCylinder
open Matrix
open scoped MatrixOrder

 

theorem positive_gram_simultaneous {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) (hB : B.PosDef) :
    ∃ V : Matrix (Fin n) (Fin n) ℝ, ∃ d : Fin n → ℝ,
      IsUnit V ∧ (∀ i, 0<d i) ∧ star V*A*V=1 ∧ star V*B*V=diagonal d := by
  obtain ⟨R,hR⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.posSemidef.nonneg
  have hdR : R.det≠0 := by
    have h := hA.det_pos
    rw [hR,det_mul,star_eq_conjTranspose,det_conjTranspose] at h
    simp only [star_trivial] at h
    intro hz
    simp [hz] at h
  have huR : IsUnit R.det := isUnit_iff_ne_zero.mpr hdR
  let T := R⁻¹
  have hRT : R*T=1 := Matrix.mul_nonsing_inv R huR
  have huT : IsUnit T := (Matrix.isUnit_iff_isUnit_det T).mpr
    (Matrix.isUnit_det_of_left_inverse hRT)
  have hTA : star T*A*T=1 := by
    calc
      _ = star (R*T)*(R*T) := by rw [hR,star_mul]; simp only [mul_assoc]
      _ = 1 := by rw [hRT]; simp
  let D := star T*B*T
  have hD : D.PosDef := by
    exact hB.conjTranspose_mul_mul_same (Matrix.mulVec_injective_iff_isUnit.mpr huT)
  let Q := hD.isHermitian.eigenvectorUnitary
  let V := T*(Q : Matrix (Fin n) (Fin n) ℝ)
  refine ⟨V,hD.isHermitian.eigenvalues,huT.mul Unitary.isUnit_coe,
    hD.eigenvalues_pos,?_,?_⟩
  · calc
      _ = star (Q : Matrix (Fin n) (Fin n) ℝ)*(star T*A*T)*Q := by
        dsimp [V]; rw [star_mul]; simp only [mul_assoc]
      _ = 1 := by rw [hTA]; simp
  · have hd := hD.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
    simp only [Unitary.conjStarAlgAut_apply] at hd
    calc
      _ = star (Q : Matrix (Fin n) (Fin n) ℝ)*D*Q := by
        dsimp [V,D]; rw [star_mul]; simp only [mul_assoc]
      _ = diagonal hD.isHermitian.eigenvalues := by simpa [Q,Function.comp_def] using hd

end PolynomialVacuumCylinder

end OAI
