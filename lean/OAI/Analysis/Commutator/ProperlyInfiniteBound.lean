import Mathlib
import OAI.Analysis.Commutator.ProperlyInfinite

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace BigOperators

open ContinuousLinearMap

universe u

namespace Kadison

variable {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma isometry_column_error_eq (P : VonNeumannAlgebra K) (h : ℕ) (v : Fin h → P)
    (Y : K →L[ℂ] K) :
    (diagonalAmplification h Y).comp (operatorRow h (fun i => (v i : K →L[ℂ] K))).adjoint-
      (operatorRow h (fun i => (v i : K →L[ℂ] K))).adjoint.comp Y =
    operatorColumn h (fun i => Y*(star (v i) : K →L[ℂ] K)-(star (v i) : K →L[ℂ] K)*Y) := by
  rw [operatorRow_adjoint]
  ext x i
  change (diagonalAmplification h Y
    (operatorColumn h (fun i => (v i : K →L[ℂ] K).adjoint) x)) i-
      (operatorColumn h (fun i => (v i : K →L[ℂ] K).adjoint) (Y x)) i = _
  rw [diagonalAmplification_apply,operatorColumn_apply,operatorColumn_apply]
  rfl

lemma isometry_column_error_bound (P : VonNeumannAlgebra K) (h : ℕ) (v : Fin h → P)
    (hv : ∀ i j, star (v i)*v j=if i=j then 1 else 0) (Y : K →L[ℂ] K) :
    ‖(diagonalAmplification h Y).comp (operatorRow h (fun i => (v i : K →L[ℂ] K))).adjoint-
      (operatorRow h (fun i => (v i : K →L[ℂ] K))).adjoint.comp Y‖ ≤
      4*commutatorSeminorm P Y := by
  rw [isometry_column_error_eq]
  exact commutator_column_bound P Y h (fun i => star (v i)) (isometry_star_columnNorm_le P h v hv)

lemma isometry_row_error_bound (P : VonNeumannAlgebra K) (h : ℕ) (v : Fin h → P)
    (hv : ∀ i j, star (v i)*v j=if i=j then 1 else 0) (Y : K →L[ℂ] K) :
    ‖Y.comp (operatorRow h (fun i => (v i : K →L[ℂ] K)))-
      (operatorRow h (fun i => (v i : K →L[ℂ] K))).comp (diagonalAmplification h Y)‖ ≤
      4*commutatorSeminorm P Y := by
  rw [←adjoint.norm_map]
  simp only [map_sub,adjoint_comp,diagonalAmplification_adjoint]
  rw [norm_sub_rev]
  have hb := isometry_column_error_bound P h v hv Y.adjoint
  simpa only [←star_eq_adjoint,commutatorSeminorm_star] using hb

lemma row_matrix_row_adjoint (P : VonNeumannAlgebra K) (h : ℕ) (v : Fin h → P)
    (X : Matrix (Fin h) (Fin h) (K →L[ℂ] K)) :
    ((operatorRow h (fun i => (v i : K →L[ℂ] K))).comp (matrixOperator h X)).comp
      (operatorRow h (fun i => (v i : K →L[ℂ] K))).adjoint =
      ∑ i, ∑ j, (v i : K →L[ℂ] K)*X i j*star (v j : K →L[ℂ] K) := by
  rw [operatorRow_adjoint]
  ext ξ
  simp only [comp_apply,operatorRow_apply,matrixOperator_apply,operatorColumn_apply,map_sum,
    sum_apply]
  rfl

lemma row_matrix_row_adjoint_mem (P : VonNeumannAlgebra K) (h : ℕ) (v : Fin h → P)
    (X : Matrix (Fin h) (Fin h) (K →L[ℂ] K)) (hX : ∀ i j,X i j∈P) :
    ((operatorRow h (fun i => (v i : K →L[ℂ] K))).comp (matrixOperator h X)).comp
      (operatorRow h (fun i => (v i : K →L[ℂ] K))).adjoint ∈P := by
  rw [row_matrix_row_adjoint]
  exact sum_mem (fun i _ => sum_mem (fun j _ => mul_mem (mul_mem (v i).property (hX i j))
    (star_mem (v j).property)))

omit [CompleteSpace K] in
lemma isometry_commutator_identity
    {L : Type*} [NormedAddCommGroup L] [NormedSpace ℂ L]
    (V : L →L[ℂ] K) (U : K →L[ℂ] L) (hUV : U.comp V=ContinuousLinearMap.id ℂ L)
    (Y : K →L[ℂ] K) (D X : L →L[ℂ] L) :
    D*X-X*D =
      (U.comp (Y*((V.comp X).comp U)-((V.comp X).comp U)*Y)).comp V-
        ((U.comp (Y.comp V-V.comp D)).comp X)-
        X.comp ((D.comp U-U.comp Y).comp V) := by
  have hc (Z : L →L[ℂ] L) : U.comp (V.comp Z)=Z := by
    rw [←comp_assoc,hUV,id_comp]
  simp only [mul_def,comp_sub,sub_comp,comp_assoc,hUV,comp_id,hc]
  abel

lemma norm_comp_contractions {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (A : F →L[ℂ] G) (B : E →L[ℂ] F) (hA : ‖A‖≤1) : ‖A.comp B‖≤‖B‖ := by
  exact (opNorm_comp_le A B).trans (by nlinarith [norm_nonneg B])

lemma norm_contractive_sandwich {E F G J : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G] [NormedAddCommGroup J] [NormedSpace ℂ J]
    (U : G →L[ℂ] J) (A : F →L[ℂ] G) (V : E →L[ℂ] F) (hU : ‖U‖≤1) (hV : ‖V‖≤1) :
    ‖(U.comp A).comp V‖≤‖A‖ := by
  calc
    _ ≤ ‖U.comp A‖*‖V‖ := opNorm_comp_le _ _
    _ ≤ ‖A‖*1 := mul_le_mul (norm_comp_contractions U A hU) hV (norm_nonneg V) (norm_nonneg A)
    _ = _ := mul_one _

omit [CompleteSpace K] in
lemma isometry_commutator_norm_bound
    {L : Type*} [NormedAddCommGroup L] [NormedSpace ℂ L]
    (V : L →L[ℂ] K) (U : K →L[ℂ] L) (hUV : U.comp V=ContinuousLinearMap.id ℂ L)
    (hV : ‖V‖≤1) (hU : ‖U‖≤1)
    (Y : K →L[ℂ] K) (D A : L →L[ℂ] L) {δ : ℝ} (hδ : 0≤δ)
    (hBF : ‖Y*((V.comp A).comp U)-((V.comp A).comp U)*Y‖≤δ*‖A‖)
    (hR : ‖Y.comp V-V.comp D‖≤4*δ) (hC : ‖D.comp U-U.comp Y‖≤4*δ) :
    ‖D*A-A*D‖≤9*δ*‖A‖ := by
  let F := (V.comp A).comp U
  let R := Y.comp V-V.comp D
  let C := D.comp U-U.comp Y
  have hleft : ‖(U.comp (Y*F-F*Y)).comp V‖≤δ*‖A‖ :=
    (norm_contractive_sandwich U _ V hU hV).trans hBF
  have hr : ‖(U.comp R).comp A‖≤(4*δ)*‖A‖ := by
    exact (opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_right
      ((norm_comp_contractions U R hU).trans hR) (norm_nonneg A))
  have hc : ‖A.comp (C.comp V)‖≤(4*δ)*‖A‖ := by
    have hcv : ‖C.comp V‖≤4*δ :=
      (opNorm_comp_le _ _).trans ((mul_le_mul hC hV (norm_nonneg V) (by positivity)).trans_eq (mul_one _))
    exact (opNorm_comp_le _ _).trans (by nlinarith [norm_nonneg A])
  rw [isometry_commutator_identity V U hUV Y D A]
  calc
    _ ≤ ‖(U.comp (Y*F-F*Y)).comp V-(U.comp R).comp A‖+‖A.comp (C.comp V)‖ := norm_sub_le _ _
    _ ≤ (‖(U.comp (Y*F-F*Y)).comp V‖+‖(U.comp R).comp A‖)+‖A.comp (C.comp V)‖ :=
      add_le_add (norm_sub_le _ _) le_rfl
    _ ≤ _ := by linarith

theorem uniform_commutator_of_isometries
    (P : VonNeumannAlgebra K) (Y : K →L[ℂ] K) (h : ℕ) (v : Fin h → P)
    (hv : ∀ i j, star (v i)*v j=if i=j then 1 else 0)
    (X : Matrix (Fin h) (Fin h) (K →L[ℂ] K)) (hX : ∀ i j,X i j∈P) :
    ‖diagonalAmplification h Y*matrixOperator h X-matrixOperator h X*diagonalAmplification h Y‖ ≤
      9*commutatorSeminorm P Y*‖matrixOperator h X‖ := by
  let V := operatorRow h (fun i => (v i : K →L[ℂ] K))
  have hV : ‖V‖≤1 := isometry_row_norm_le P h v hv
  have hU : ‖V.adjoint‖≤1 := by simpa only [adjoint.norm_map] using hV
  apply isometry_commutator_norm_bound V V.adjoint (isometry_row_adjoint_comp P h v hv) hV hU
    Y (diagonalAmplification h Y) (matrixOperator h X) (commutatorSeminorm_nonneg P Y)
  · exact (commutator_bound P Y (row_matrix_row_adjoint_mem P h v X hX)).trans
      (mul_le_mul_of_nonneg_left (norm_contractive_sandwich V (matrixOperator h X) V.adjoint hV hU)
        (commutatorSeminorm_nonneg P Y))
  · exact isometry_row_error_bound P h v hv Y
  · exact isometry_column_error_bound P h v hv Y

end Kadison

end

end
end

end OAI
