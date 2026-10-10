import OAI.Geometry.Relativity.CKS.SourcePhysicalFoliation
import OAI.Geometry.Relativity.CKS.CollarRadialFields
import OAI.Geometry.Relativity.CKS.InducedSphereCalculus

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix

lemma foliationMetric_recovery {a : ℝ} {b : Point} {q : Mat}
    (hp : (metricBlock a b q).PosDef) :
    foliationMetric (1/Real.sqrt (a-∑ i, ∑ k, inverse q i k*(b i*b k))) q
      (fun i => ∑ k, inverse q i k*b k)=metricBlock a b q := by
  have hq : determinant q ≠ 0 := by
    rw [determinant_eq]
    exact (metricBlock_leaf_posDef hp).det_pos.ne'
  have hschur := metricBlock_schur_positive hp
  have hr : 1/(1/Real.sqrt (a-∑ i, ∑ k, inverse q i k*(b i*b k)))^2 =
      a-∑ i, ∑ k, inverse q i k*(b i*b k) := by
    simp only [one_div,inv_pow,inv_inv,Real.sq_sqrt hschur.le]
  unfold foliationMetric
  rw [hr,inverse_quadratic q hq]
  simp only [sub_add_cancel]
  congr 1
  funext i
  exact inverse_mul_vector q hq b i

lemma foliationTensor_recovery {U : ℝ} (hU : U ≠ 0) (a : ℝ) (b : Point) {q : Mat}
    (hq : q.IsHermitian) (s : Point) :
    foliationTensor U
      (U^2*(a-2*∑ i, s i*b i+∑ i, ∑ j, q i j*(s i*s j)))
      (fun i => U*(b i-∑ j, s j*q j i)) q s=metricBlock a b q := by
  have hqs := hermitian_real_symmetry hq 0 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [foliationTensor,metricBlock,Matrix.of_apply,Fin.sum_univ_two]
  all_goals rw [hqs]
  all_goals field_simp
  all_goals ring
end
end CKSAngularGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Matrix CKSAngularGeometry

lemma source_metric_recovery {f : SourceMassFields} {y : Point}
    (hp : (sourceMetric f y).PosDef) :
    foliationMetric (sourceLapse f y) (sourceGamma f y) (sourceShift f y)=sourceMetric f y :=
  foliationMetric_recovery hp

lemma source_tensor_recovery {f : SourceTensorFields} {y : Point}
    (hp : (sourceMetric f.base y).PosDef) (hk : (sourceTensor f y).IsHermitian) :
    foliationTensor (sourceLapse f.base y) (sourceOriginalL f y)
      (sourceOriginalEta f y) (sourceTangentialK f.base y) (sourceShift f.base y)=sourceTensor f y := by
  have hs : 0 < sourceSchur f.base y := metricBlock_schur_positive hp
  have hU : sourceLapse f.base y ≠ 0 := by
    exact one_div_ne_zero (Real.sqrt_ne_zero'.mpr hs)
  have hq : (sourceTangentialK f.base y).IsHermitian := by
    simpa only [sourceTensor,metricBlock_submatrix] using hk.submatrix Fin.succ
  exact foliationTensor_recovery hU _ _ hq _

end
end CKSMixedGeometry

end

end OAI
