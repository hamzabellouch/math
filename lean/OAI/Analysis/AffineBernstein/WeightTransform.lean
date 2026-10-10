import Mathlib
import OAI.Analysis.AffineBernstein.LogMassWeight
import OAI.Analysis.AffineBernstein.AffineFamily
import OAI.Analysis.AffineBernstein.TubeLinearTransform

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
section DependencyScope
open Filter
open scoped Topology

section WeightTransform
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma tubeLogMassWeight_eq {k : ℕ} (H : Space k × E → ℝ) (q : Space k × E)
    (hs : ∀ i, q.1 i ≠ 0) :
    tubeLogMassWeight H q = 1 + ∑ i, H q *
      (tubeBaseMatrix H q (EuclideanSpace.basisFun (Fin k) ℝ).toBasis)⁻¹ i i/(q.1 i)^2 := by
  simp only [tubeLogMassWeight,tubeBasePair_coordinate_log H q _ (hs _)]

lemma matrix_inverse_diagonal_congruence {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (d : ι → ℝ) (hd : ∀ i, d i ≠ 0) (i j : ι) :
    (Matrix.diagonal d*A*Matrix.diagonal d)⁻¹ i j = (d i)⁻¹*A⁻¹ i j*(d j)⁻¹ := by
  have hi : (Matrix.diagonal d)⁻¹ = Matrix.diagonal (fun i => (d i)⁻¹) := by
    apply Matrix.inv_eq_right_inv
    simp [Matrix.diagonal_mul_diagonal,hd]
  rw [Matrix.mul_inv_rev,Matrix.mul_inv_rev,hi]
  simp [Matrix.diagonal_mul,Matrix.mul_diagonal,mul_assoc]

omit [CompleteSpace E] in
lemma tubeLogMassWeight_diagonal_comp {k : ℕ} (B : Space k →L[ℝ] Space k) (A : E →L[ℝ] E)
    (d : Fin k → ℝ) (hd : ∀ i, d i ≠ 0) (hBd : ∀ s i, B s i = d i*s i)
    {H : Space k × E → ℝ} {q : Space k × E}
    (hH : ContDiffAt ℝ ∞ H (B q.1,A q.2)) (hs : ∀ i, q.1 i ≠ 0) :
    tubeLogMassWeight (fun z => H (B z.1,A z.2)) q =
      tubeLogMassWeight H (B q.1,A q.2) := by
  let b := (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
  have hM : LinearMap.toMatrix b b B.toLinearMap = Matrix.diagonal d := by
    ext i j
    simp [b,LinearMap.toMatrix_apply,EuclideanSpace.basisFun_repr,hBd,
      EuclideanSpace.basisFun_apply,PiLp.single_apply,Matrix.diagonal_apply]
  have hb : tubeBaseMatrix (fun z => H (B z.1,A z.2)) q b =
      Matrix.diagonal d*tubeBaseMatrix H (B q.1,A q.2) b*Matrix.diagonal d := by
    rw [tubeBaseMatrix_linear_comp B A hH b,hM,Matrix.diagonal_transpose]
  rw [tubeLogMassWeight_eq _ q hs,tubeLogMassWeight_eq _ (B q.1,A q.2)
    (fun i => by dsimp; rw [hBd]; exact mul_ne_zero (hd i) (hs i))]
  change 1 + ∑ i, H (B q.1,A q.2) * (tubeBaseMatrix (fun z => H (B z.1,A z.2)) q b)⁻¹ i i / (q.1 i)^2 = _
  rw [hb]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [matrix_inverse_diagonal_congruence _ d hd]
  dsimp only
  rw [hBd]
  field_simp
  rfl

lemma tubeLogMassWeight_homogeneous {k : ℕ} {K : Space k → Set E} {s : Space k} {e : E}
    {D : Set (Space k)} (hD : IsOpen D) (hs : s ∈ D)
    (hK : ∀ y ∈ D, IsCompact (K y)) (hne : ∀ y ∈ D, (K y).Nonempty)
    {c : ℝ} (hc : 0 < c)
    (hH : ContDiffAt ℝ ∞ (fun q : Space k × E => homogeneousSupport (K q.1) q.2) (s,e))
    (hHc : ContDiffAt ℝ ∞ (fun q : Space k × E => homogeneousSupport (K q.1) q.2) (s,c • e))
    (hs0 : ∀ i, s i ≠ 0)
    (hB : (tubeBaseMatrix (fun q : Space k × E => homogeneousSupport (K q.1) q.2) (s,e)
      (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det ≠ 0) :
    tubeLogMassWeight (fun q : Space k × E => homogeneousSupport (K q.1) q.2) (s,c • e) =
      tubeLogMassWeight (fun q : Space k × E => homogeneousSupport (K q.1) q.2) (s,e) := by
  let : Invertible c := invertibleOfNonzero hc.ne'
  rw [tubeLogMassWeight_eq _ _ hs0,tubeLogMassWeight_eq _ _ hs0]
  dsimp only
  rw [homogeneousSupport_smul (hK s hs) (hne s hs) e hc,
    homogeneous_tubeBaseMatrix_scale hD hs hK hne hc hH hHc,
    Matrix.inv_smul _ _ (isUnit_iff_ne_zero.mpr hB),invOf_eq_inv]
  simp only [Matrix.smul_apply,smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  field_simp
end WeightTransform





end DependencyScope
end AffineBernstein
end

end OAI
