import OAI.Geometry.Relativity.CKS.LogPhysicalFoliation
import OAI.Geometry.Relativity.CKS.SourceMassRegularity

namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter Matrix
open CKSAngularGeometry (determinant inverse determinant_eq)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def sourceLapse (f : SourceMassFields) : Point → ℝ := fun y => 1/Real.sqrt (sourceSchur f y)
def sourceU (f : SourceMassFields) : Point → ℝ := fun y => sourceLapse f y*sourceExpansion f y
def sourceT (f : SourceMassFields) : Point → ℝ := fun y =>
  (1/2:ℝ)*traceProduct (inverse (sourceGamma f y)) (sourceTangentialK f y)

lemma sourceLapse_regular {f : SourceMassFields} {y : Point} (hf : f.RegularAt y) (hy : y 0 ≠ 0)
    (hp : (sourceMetric f y).PosDef) : ContDiffAt ℝ 2 (sourceLapse f) y := by
  have h0 : determinant (sourceGamma f y) ≠ 0 := by
    rw [determinant_eq]
    exact (CKSAngularGeometry.metricBlock_leaf_posDef hp).det_pos.ne'
  have hs : 0 < sourceSchur f y := CKSAngularGeometry.metricBlock_schur_positive hp
  exact contDiffAt_const.fun_div ((sourceSchur_regular hf hy h0).sqrt hs.ne')
    (Real.sqrt_ne_zero'.mpr hs)
lemma sourceU_regular {f : SourceMassFields} {y : Point} (hf : f.RegularAt y) (hy : y 0 ≠ 0)
    (hp : (sourceMetric f y).PosDef) : ContDiffAt ℝ 2 (sourceU f) y := by
  have h0 : determinant (sourceGamma f y) ≠ 0 := by
    rw [determinant_eq]
    exact (CKSAngularGeometry.metricBlock_leaf_posDef hp).det_pos.ne'
  exact (sourceLapse_regular hf hy hp).mul (sourceExpansion_regular hf hy h0)
lemma sourceT_regular {f : SourceMassFields} {y : Point} (hf : f.RegularAt y) (hy : y 0 ≠ 0)
    (hp : (sourceMetric f y).PosDef) : ContDiffAt ℝ 2 (sourceT f) y := by
  have h0 : determinant (sourceGamma f y) ≠ 0 := by
    rw [determinant_eq]
    exact (CKSAngularGeometry.metricBlock_leaf_posDef hp).det_pos.ne'
  have hi := inverse_diff_at ((sourceGamma_regular hf hy).of_le (by norm_num : (2:ℕ∞ω) ≤ 3)) h0
  exact contDiffAt_const.mul (traceProduct_diff hi (sourceTangentialK_regular hf hy))

lemma sourceLapse_pullback (f : SourceMassFields) :
    (fun y => sourceLapse f (logRadiusChart y)) = logLapse f.logFields := by
  funext y
  unfold sourceLapse logLapse
  rw [congrFun (sourceSchur_pullback f) y]
lemma sourceT_pullback (f : SourceMassFields) :
    (fun y => sourceT f (logRadiusChart y)) = logT f.logFields := by
  funext y
  unfold sourceT logT
  rw [congrFun (sourceGamma_pullback f) y,congrFun (sourceTangentialK_pullback f) y]

lemma sourceU_pullback {f : SourceMassFields} {x : Point}
    (hf : f.RegularAt (logRadiusChart x))
    (h0 : determinant (sourceGamma f (logRadiusChart x)) ≠ 0) :
    sourceU f (logRadiusChart x) = logU f.logFields x := by
  unfold sourceU logU
  rw [congrFun (sourceLapse_pullback f) x,sourceExpansion_pullback hf h0]

end
end CKSMixedGeometry

end

end OAI
