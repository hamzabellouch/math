import Mathlib
import OAI.Analysis.MatrixSigning.Matrices.SandwichCLM

namespace OAI

open Matrix

namespace CurrentKS.Hermitian
noncomputable section
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder

variable {d : ℕ}
section Operator
open scoped Matrix.Norms.L2Operator

lemma square_scalar_bound (A : H d) {a : ℝ} (ha : 0 ≤ a)
    (hApos : A ∈ psdCone d) (hA : A ≤ a • (Hermitian.one : H d)) :
    sandwich A Hermitian.one ≤ a^2 • (Hermitian.one : H d) := by
  let : CStarAlgebra (Mat d) := {}
  have hnorm : ‖(A : Mat d)‖ ≤ a := by
    apply (CStarAlgebra.norm_le_iff_le_algebraMap (A : Mat d) ha hApos.nonneg).mpr
    simp only [Algebra.algebraMap_eq_smul_one]
    exact hA
  have hsqpos : ((A : Mat d)*(A : Mat d)).PosSemidef := by
    have hh : ((sandwich A Hermitian.one : H d) : Mat d).PosSemidef :=
      sandwich_psd A Hermitian.one one_mem_psdCone
    simpa only [sandwich_val, one_val, mul_one] using hh
  have hsqnorm : ‖(A : Mat d)*(A : Mat d)‖ ≤ a^2 :=
    (norm_mul_le _ _).trans (by nlinarith [norm_nonneg (A : Mat d)])
  have hb := (CStarAlgebra.norm_le_iff_le_algebraMap ((A : Mat d)*(A : Mat d))
    (sq_nonneg a) hsqpos.nonneg).mp hsqnorm
  change (A : Mat d)*1*(A : Mat d) ≤ (a^2 : ℝ) • (1 : Mat d)
  simpa only [Algebra.algebraMap_eq_smul_one, mul_one] using hb

end Operator

lemma inverse_lower_of_upper (X : H d) (hX : X ∈ pd d) {a : ℝ} (ha : 0 < a)
    (h : X ≤ a • (Hermitian.one : H d)) : a⁻¹ • (Hermitian.one : H d) ≤ invH X := by
  exact inverse_bound_below ha hX.inv (by rwa [invH_involutive X hX])

lemma inverse_upper_of_lower (X : H d) (hX : X ∈ pd d) {a : ℝ} (ha : 0 < a)
    (h : a • (Hermitian.one : H d) ≤ X) : invH X ≤ a⁻¹ • (Hermitian.one : H d) := by
  have hi := inverse_antitone (scalar_posDef ha) hX h
  rw [scalar_inv] at hi
  change (X : Mat d)⁻¹ ≤ ((a⁻¹ : ℝ) : ℂ) • (1 : Mat d)
  simpa only [Complex.ofReal_inv] using hi

end
end CurrentKS.Hermitian

end OAI
