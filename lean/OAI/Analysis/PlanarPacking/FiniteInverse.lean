import OAI.Analysis.PlanarPacking.Certificate.WCertificates
import OAI.Analysis.PlanarPacking.MatrixInverse

namespace OAI

/-!
# Inverse bounds for the central interpolation block

Exact rational approximate inverses give bounds for the two central blocks.
-/

namespace SharpPlanar.Numerical
lemma defectplus_norm : ‖1-(matrixL1 Wplus)*(matrixL1 Aplus)‖ < (1:ℝ)/1000 := by
  have hh := matrixL1_norm_lt defectplus_column
  rw [matrixL1_sub,matrixL1_one,matrixL1_mul] at hh
  exact hh
lemma defectminus_norm : ‖1-(matrixL1 Wminus)*(matrixL1 Aminus)‖ < (1:ℝ)/1000 := by
  have hh := matrixL1_norm_lt defectminus_column
  rw [matrixL1_sub,matrixL1_one,matrixL1_mul] at hh
  exact hh
lemma Wplus_norm : ‖matrixL1 Wplus‖ < (3084:ℝ)/100 := matrixL1_norm_lt Wplus_column
lemma Wminus_norm : ‖matrixL1 Wminus‖ < (183:ℝ)/100 := matrixL1_norm_lt Wminus_column
lemma defectplus_lt_one : ‖1-(matrixL1 Wplus)*(matrixL1 Aplus)‖ < 1 :=
  defectplus_norm.trans (by norm_num)
lemma defectminus_lt_one : ‖1-(matrixL1 Wminus)*(matrixL1 Aminus)‖ < 1 :=
  defectminus_norm.trans (by norm_num)
noncomputable def inversePlusEquiv : L1Finite (Fin 6) ≃L[ℝ] L1Finite (Fin 6) :=
  (certifiedEquiv (matrixL1 Aplus) (matrixL1 Wplus) defectplus_lt_one).symm
noncomputable def inverseMinusEquiv : L1Finite (Fin 6) ≃L[ℝ] L1Finite (Fin 6) :=
  (certifiedEquiv (matrixL1 Aminus) (matrixL1 Wminus) defectminus_lt_one).symm
lemma inversePlus_apply (x : L1Finite (Fin 6)) :
    matrixL1 Aplus (inversePlusEquiv x) = x :=
  (certifiedEquiv (matrixL1 Aplus) (matrixL1 Wplus) defectplus_lt_one).apply_symm_apply x
lemma inverseMinus_apply (x : L1Finite (Fin 6)) :
    matrixL1 Aminus (inverseMinusEquiv x) = x :=
  (certifiedEquiv (matrixL1 Aminus) (matrixL1 Wminus) defectminus_lt_one).apply_symm_apply x
lemma inversePlus_norm : ‖inversePlusEquiv.toContinuousLinearMap‖ < 32 := by
  have hh := certified_inverse_norm_le (matrixL1 Aplus) (matrixL1 Wplus)
    (by norm_num : (1:ℝ)/1000 < 1) defectplus_norm.le
  change ‖inversePlusEquiv.toContinuousLinearMap‖ ≤ _ at hh
  apply hh.trans_lt
  apply (div_lt_iff₀ (by norm_num : (0:ℝ) < 1-1/1000)).mpr
  nlinarith [Wplus_norm]
lemma inverseMinus_norm : ‖inverseMinusEquiv.toContinuousLinearMap‖ < 32 := by
  have hh := certified_inverse_norm_le (matrixL1 Aminus) (matrixL1 Wminus)
    (by norm_num : (1:ℝ)/1000 < 1) defectminus_norm.le
  change ‖inverseMinusEquiv.toContinuousLinearMap‖ ≤ _ at hh
  apply hh.trans_lt
  apply (div_lt_iff₀ (by norm_num : (0:ℝ) < 1-1/1000)).mpr
  nlinarith [Wminus_norm]
end SharpPlanar.Numerical

end OAI
