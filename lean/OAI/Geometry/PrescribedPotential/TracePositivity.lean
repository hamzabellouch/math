import Mathlib

namespace OAI

/-! Trace Positivity. -/

section

noncomputable section
open Matrix
open scoped ComplexOrder MatrixOrder
namespace KaehlerCalculus
variable {n : ℕ}

lemma trace_mul_real {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ((A*B).trace.re : ℂ) = (A*B).trace := by
  have he : star (A*B).trace = (A*B).trace := by
    rw [← Matrix.trace_conjTranspose,Matrix.conjTranspose_mul,hA.eq,hB.eq,Matrix.trace_mul_comm]
  apply Complex.ext
  · simp
  · have hi := congrArg Complex.im he
    simp only [Complex.star_def,Complex.conj_im] at hi
    simp only [Complex.ofReal_im]
    linarith

lemma trace_mul_pos [Nonempty (Fin n)] {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosDef) (hB : B.PosDef) : 0 < (A*B).trace.re := by
  obtain ⟨Q,hQ,rfl⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp hA.isStrictlyPositive
  have h := (hB.mul_mul_conjTranspose_same (Matrix.vecMul_injective_iff_isUnit.mpr hQ)).trace_pos
  change 0 < (Qᴴ*Q*B).trace.re
  rw [Matrix.trace_mul_cycle] at h
  exact (Complex.pos_iff.mp h).1

lemma whitening (M : Matrix (Fin n) (Fin n) ℂ) (hM : M.PosDef) :
    ∃ B : Matrix (Fin n) (Fin n) ℂ, IsUnit B ∧ Bᴴ*M*B = 1 := by
  obtain ⟨Q,hQ,hM⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp hM.isStrictlyPositive
  obtain ⟨Q,rfl⟩ := hQ
  let R : Matrix (Fin n) (Fin n) ℂ := ↑(Q⁻¹)
  have hQR : (Q : Matrix (Fin n) (Fin n) ℂ)*R = 1 := Q.mul_inv
  refine ⟨R,(Q⁻¹).isUnit,?_⟩
  rw [hM]
  change Rᴴ*((Q : Matrix (Fin n) (Fin n) ℂ)ᴴ*(Q : Matrix (Fin n) (Fin n) ℂ))*R = 1
  rw [Matrix.mul_assoc Rᴴ,Matrix.mul_assoc, hQR,Matrix.mul_one,
    ← Matrix.conjTranspose_mul,hQR,Matrix.conjTranspose_one]
end KaehlerCalculus

end
end

end OAI
