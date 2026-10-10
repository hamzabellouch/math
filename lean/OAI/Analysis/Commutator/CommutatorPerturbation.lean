import Mathlib
import OAI.Analysis.Commutator.MainCommutantDistance

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma commutatorSeminorm_le (P : VonNeumannAlgebra H) (Y : H →L[ℂ] H) (C : ℝ)
    (hC : ∀ a : H →L[ℂ] H,a∈P → ‖a‖≤1 → ‖Y*a-a*Y‖≤C) :
    commutatorSeminorm P Y≤C := by
  apply csSup_le
  · exact ⟨0,0,P.zero_mem,by simp,by simp⟩
  · rintro r ⟨a,ha,hna,rfl⟩
    exact hC a ha hna

lemma commutatorSeminorm_perturb (P : VonNeumannAlgebra H) (Y Z : H →L[ℂ] H) :
    commutatorSeminorm P Z≤commutatorSeminorm P Y+2*‖Z-Y‖ := by
  apply commutatorSeminorm_le
  intro a ha hna
  have he : Z*a-a*Z=(Y*a-a*Y)+((Z-Y)*a-a*(Z-Y)) := by
    simp only [sub_mul,mul_sub]; abel
  rw [he]
  calc
    _ ≤ ‖Y*a-a*Y‖+‖(Z-Y)*a-a*(Z-Y)‖ := norm_add_le _ _
    _ ≤ commutatorSeminorm P Y+2*‖Z-Y‖*‖a‖ :=
      add_le_add (commutator_bound_unitball P Y ha hna) (operator_commutator_norm_le _ _)
    _ ≤ commutatorSeminorm P Y+2*‖Z-Y‖ := by nlinarith [norm_nonneg (Z-Y)]

lemma commutatorSeminorm_three (P : VonNeumannAlgebra H) (Y Z : H →L[ℂ] H)
    (hZ : ‖Z-Y‖≤commutatorSeminorm P Y) : commutatorSeminorm P Z≤3*commutatorSeminorm P Y := by
  have hh := commutatorSeminorm_perturb P Y Z
  linarith

lemma matrix_commutator_perturb (P : VonNeumannAlgebra H) (Y Z : H →L[ℂ] H)
    (hZ : ‖Z-Y‖≤commutatorSeminorm P Y) (c : ℝ) (hc : 0≤c)
    (h : ℕ) (X : Matrix (Fin h) (Fin h) (H →L[ℂ] H))
    (hb : ‖diagonalAmplification h Z*matrixOperator h X-matrixOperator h X*diagonalAmplification h Z‖ ≤
      c*commutatorSeminorm P Z*‖matrixOperator h X‖) :
    ‖diagonalAmplification h Y*matrixOperator h X-matrixOperator h X*diagonalAmplification h Y‖ ≤
      (3*c+2)*commutatorSeminorm P Y*‖matrixOperator h X‖ := by
  let A := matrixOperator h X
  have he : diagonalAmplification h Y*A-A*diagonalAmplification h Y=
      (diagonalAmplification h Z*A-A*diagonalAmplification h Z)+
      (diagonalAmplification h (Y-Z)*A-A*diagonalAmplification h (Y-Z)) := by
    rw [diagonalAmplification_sub,sub_mul,mul_sub]
    abel
  have hdelta : ‖Y-Z‖≤commutatorSeminorm P Y := by rwa [norm_sub_rev]
  have herr := (operator_commutator_norm_le (diagonalAmplification h (Y-Z)) A).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left ((diagonalAmplification_norm_le h (Y-Z)).trans hdelta) (by norm_num))
      (norm_nonneg A))
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (commutatorSeminorm_three P Y Z hZ) hc) (norm_nonneg A)
  change ‖diagonalAmplification h Y*A-A*diagonalAmplification h Y‖≤_
  rw [he]
  calc
    _ ≤ ‖diagonalAmplification h Z*A-A*diagonalAmplification h Z‖+
      ‖diagonalAmplification h (Y-Z)*A-A*diagonalAmplification h (Y-Z)‖ := norm_add_le _ _
    _ ≤ c*(3*commutatorSeminorm P Y)*‖A‖+2*commutatorSeminorm P Y*‖A‖ :=
      add_le_add (hb.trans hh) herr
    _ = _ := by dsimp [A]; ring

end Kadison

end

end
end

end OAI
