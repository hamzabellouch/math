import OAI.Geometry.NodalSets.Elliptic.BallPacking
import OAI.Geometry.NodalSets.Hausdorff.NodalProjection

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set
noncomputable section

abbrev TransverseCoord := Fin 3 → ℝ

def transverseProjection (j : Fin 4) : Coord →L[ℝ] TransverseCoord :=
  ContinuousLinearMap.pi (fun k ↦ ContinuousLinearMap.proj (j.succAbove k))

def transverseInclusion (j : Fin 4) : TransverseCoord →L[ℝ] Coord where
  toFun := Fin.insertNth (α := fun _ : Fin 4 ↦ ℝ) j 0
  map_add' := by
    intro x y
    ext k
    induction k using j.succAboveCases <;> simp
  map_smul' := by
    intro a x
    ext k
    induction k using j.succAboveCases <;> simp
  cont := by
    apply continuous_pi
    intro k
    induction k using j.succAboveCases
    · simpa using (continuous_const : Continuous (fun _ : TransverseCoord ↦ (0:ℝ)))
    · simpa using continuous_apply _

def transverseDisk (r : ℝ) : Set TransverseCoord :=
  {z | Real.sqrt (∑ k : Fin 3, (z k)^2) ≤ r}

lemma transverseProjection_inclusion (j : Fin 4) (z : TransverseCoord) :
    transverseProjection j (transverseInclusion j z) = z := by
  ext k
  exact Fin.insertNth_apply_succAbove (α := fun _ : Fin 4 ↦ ℝ) j 0 z k

lemma transverseProjection_axis (j : Fin 4) (a : ℝ) :
    transverseProjection j (a • Pi.single j 1) = 0 := by
  ext k
  simp [transverseProjection,Fin.succAbove_ne]

lemma transverseInclusion_sourceNorm (j : Fin 4) (z : TransverseCoord) :
    sourceEuclideanNorm (transverseInclusion j z) = Real.sqrt (∑ k : Fin 3, (z k)^2) := by
  unfold sourceEuclideanNorm
  rw [Fin.sum_univ_succAbove _ j]
  simp [transverseInclusion]

lemma transverseProjection_lipschitz (j : Fin 4) : LipschitzWith 1 (transverseProjection j) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm,dist_eq_norm,NNReal.coe_one,one_mul]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg (x-y))).mpr
  intro k
  exact norm_le_pi_norm (x-y) (j.succAbove k)

end
end Yau.Geometry

end OAI
