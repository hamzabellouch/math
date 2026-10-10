import Mathlib
import OAI.Analysis.MatrixSigning.Potential.NormSq

namespace OAI

open Matrix

namespace CurrentKS.Variational
noncomputable section
open CurrentKS.Hermitian Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

private local instance : NormedAddCommGroup (H d) := inferInstance
private local instance : NormedSpace ℝ (H d) := inferInstance
private local instance : TopologicalSpace (H d) :=
  (inferInstance : NormedAddCommGroup (H d)).toUniformSpace.toTopologicalSpace
private local instance : NormedAddCommGroup (Pair d) := inferInstance
private local instance : NormedSpace ℝ (Pair d) := inferInstance
private local instance : TopologicalSpace (Pair d) :=
  (inferInstance : NormedAddCommGroup (Pair d)).toUniformSpace.toTopologicalSpace
private local instance : NormedAddCommGroup (PairHilbert d) := inferInstance
private local instance : NormedSpace ℝ (PairHilbert d) := inferInstance
private local instance : TopologicalSpace (PairHilbert d) :=
  (inferInstance : NormedAddCommGroup (PairHilbert d)).toUniformSpace.toTopologicalSpace
private local instance : NormedAddCommGroup (Vars d) := inferInstance
private local instance : NormedSpace ℝ (Vars d) := inferInstance
private local instance : TopologicalSpace (Vars d) :=
  (inferInstance : NormedAddCommGroup (Vars d)).toUniformSpace.toTopologicalSpace

lemma norm_tCoord_le : norm (E := Vars d →L[ℝ] ℝ) (tCoord d) ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  simp only [one_mul]
  exact norm_fst_le z
lemma norm_uCoord_le : norm (E := Vars d →L[ℝ] PairHilbert d) (uCoord d) ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  simp only [one_mul]
  exact (norm_fst_le z.2).trans (norm_snd_le z)
lemma norm_pCoord_le : norm (E := Vars d →L[ℝ] PairHilbert d) (pCoord d) ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  simp only [one_mul]
  exact (norm_snd_le z.2).trans (norm_snd_le z)
lemma norm_xCoord_le : norm (E := Vars d →L[ℝ] H d) (xCoord d) ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  simp only [one_mul]
  exact (WithLp.norm_fst_le (H d) z.2.1).trans
    ((norm_fst_le z.2).trans (norm_snd_le z))
lemma norm_yCoord_le : norm (E := Vars d →L[ℝ] H d) (yCoord d) ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  simp only [one_mul]
  exact (WithLp.norm_snd_le (H d) z.2.1).trans
    ((norm_fst_le z.2).trans (norm_snd_le z))
lemma norm_mCoord_le : norm (E := Vars d →L[ℝ] H d) (mCoord d) ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  simp only [one_mul]
  exact (WithLp.norm_fst_le (H d) z.2.2).trans
    ((norm_snd_le z.2).trans (norm_snd_le z))
lemma norm_nCoord_le : norm (E := Vars d →L[ℝ] H d) (nCoord d) ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  simp only [one_mul]
  exact (WithLp.norm_snd_le (H d) z.2.2).trans
    ((norm_snd_le z.2).trans (norm_snd_le z))

lemma norm_pairEquiv_symm_le : norm (E := Pair d →L[ℝ] PairHilbert d) (pairEquiv d).symm.toContinuousLinearMap ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro z
  have he : ‖(pairEquiv d).symm z‖^2 = ‖z.1‖^2+‖z.2‖^2 := WithLp.prod_norm_sq_eq_of_L2 _
  have h₁ := pow_le_pow_left₀ (norm_nonneg z.1) (norm_fst_le z) 2
  have h₂ := pow_le_pow_left₀ (norm_nonneg z.2) (norm_snd_le z) 2
  change ‖(pairEquiv d).symm z‖ ≤ 2*‖z‖
  nlinarith [norm_nonneg ((pairEquiv d).symm z),norm_nonneg z]

lemma norm_one_le_dimension : ‖(Hermitian.one : H d)‖ ≤ (d:ℝ)+1 := by
  have hn := norm_one_sq (d := d)
  have hd := Nat.cast_nonneg (α := ℝ) d
  nlinarith [norm_nonneg (Hermitian.one : H d)]

lemma norm_identityPair_le_dimension : ‖identityPair d‖ ≤ 2*((d:ℝ)+1) := by
  have hn := identityPair_norm_sq (d := d)
  have hd := Nat.cast_nonneg (α := ℝ) d
  nlinarith [norm_nonneg (identityPair d)]

end
end CurrentKS.Variational

end OAI
