import OAI.Geometry.Relativity.CKS.LogPhysicalTensor
import OAI.Geometry.Relativity.CKS.SourceMassRegularity
import OAI.Geometry.Relativity.CKS.CollarLogSlices

namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter Matrix
open CKSAngularGeometry (determinant inverse determinant_eq)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

structure SourceTensorFields where
  base : SourceMassFields
  kr : Point → ℝ
  kb : Point → A → ℝ

structure SourceTensorFields.RegularAt (f : SourceTensorFields) (x : Point) : Prop where
  base : f.base.RegularAt x
  kr : ContDiffAt ℝ 2 f.kr x
  kb : ContDiffAt ℝ 2 f.kb x

structure SourceTensorFields.ComponentBounds (f : SourceTensorFields) (B : ℝ) (y : Point) : Prop where
  base : f.base.ComponentBounds B y
  kr : ScaledComponentBound f.kr 2 5 B y
  kb : ∀ a, ScaledComponentBound (fun z => f.kb z a) 2 3 B y

def SourceTensorFields.logFields (f : SourceTensorFields) : TensorFields where
  base := f.base.logFields
  kr := fun y => f.kr (logRadiusChart y)
  kb := fun y => f.kb (logRadiusChart y)

def sourceRadialK (f : SourceTensorFields) : Point → ℝ := fun y => 1/(1+(y 0)^2)+f.kr y

def sourceOriginalL (f : SourceTensorFields) : Point → ℝ := fun y =>
  (1/Real.sqrt (sourceSchur f.base y))^2*(sourceRadialK f y-
    2*∑ a, sourceShift f.base y a*f.kb y a+
    ∑ a, ∑ b, sourceTangentialK f.base y a b*(sourceShift f.base y a*sourceShift f.base y b))

def sourceOriginalEta (f : SourceTensorFields) : Point → A → ℝ := fun y a =>
  (1/Real.sqrt (sourceSchur f.base y))*(f.kb y a-∑ b, sourceShift f.base y b*sourceTangentialK f.base y b a)

def sourceOriginalTau (f : SourceTensorFields) : Point → Mat := fun y =>
  sourceTangentialK f.base y-
    (traceProduct (inverse (sourceGamma f.base y)) (sourceTangentialK f.base y)/2) • sourceGamma f.base y

lemma source_tensor_log_regular {f : SourceTensorFields} {x : Point} (hf : f.RegularAt (logRadiusChart x)) :
    f.logFields.RegularAt x := by
  have hc := (logRadiusChart_smooth.contDiffAt (x := x)).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  exact ⟨source_logFields_regular hf.base,hf.kr.comp x hc,hf.kb.comp x hc⟩

lemma sourceOriginalL_pullback (f : SourceTensorFields) :
    (fun y => sourceOriginalL f (logRadiusChart y)) = logOriginalL f.logFields := by
  funext y
  unfold sourceOriginalL logOriginalL
  have hs := congrFun (sourceSchur_pullback f.base) y
  have hshift := congrFun (sourceShift_pullback f.base) y
  have hk := congrFun (sourceTangentialK_pullback f.base) y
  rw [hs,hshift,hk]
  rfl

lemma sourceOriginalEta_pullback (f : SourceTensorFields) :
    (fun y => sourceOriginalEta f (logRadiusChart y)) = logOriginalEta f.logFields := by
  funext y a
  unfold sourceOriginalEta logOriginalEta
  have hs := congrFun (sourceSchur_pullback f.base) y
  have hshift := congrFun (sourceShift_pullback f.base) y
  have hk := congrFun (sourceTangentialK_pullback f.base) y
  rw [hs,hshift,hk]
  rfl

lemma sourceOriginalTau_pullback (f : SourceTensorFields) :
    (fun y => sourceOriginalTau f (logRadiusChart y)) = logOriginalTau f.logFields := by
  funext y
  unfold sourceOriginalTau logOriginalTau
  have hq := congrFun (sourceGamma_pullback f.base) y
  have hk := congrFun (sourceTangentialK_pullback f.base) y
  rw [hq,hk]
  rfl

lemma sourceRadialK_regular {f : SourceTensorFields} {y : Point} (hf : f.RegularAt y) :
    ContDiffAt ℝ 2 (sourceRadialK f) y := by
  have hh : ContDiffAt ℝ 2 (fun z : Point => 1+(z 0)^2) y := by fun_prop
  exact (contDiffAt_const.fun_div hh (by positivity)).add hf.kr

lemma sourceOriginalL_regular {f : SourceTensorFields} {y : Point}
    (hf : f.RegularAt y) (hy : y 0 ≠ 0) (hp : (sourceMetric f.base y).PosDef) :
    ContDiffAt ℝ 2 (sourceOriginalL f) y := by
  have h0 : determinant (sourceGamma f.base y) ≠ 0 := by
    rw [determinant_eq]
    exact (CKSAngularGeometry.metricBlock_leaf_posDef hp).det_pos.ne'
  have hs : 0 < sourceSchur f.base y := CKSAngularGeometry.metricBlock_schur_positive hp
  have hshift := (sourceShift_regular hf.base hy h0).of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have hk := sourceTangentialK_regular hf.base hy
  have hU : ContDiffAt ℝ 2 (fun z => 1/Real.sqrt (sourceSchur f.base z)) y :=
    contDiffAt_const.fun_div ((sourceSchur_regular hf.base hy h0).sqrt hs.ne') (Real.sqrt_ne_zero'.mpr hs)
  exact (hU.pow 2).mul (((sourceRadialK_regular hf).sub (contDiffAt_const.mul
    (ContDiffAt.sum fun a _ => (contDiffAt_pi.mp hshift a).mul (contDiffAt_pi.mp hf.kb a)))).add
      (ContDiffAt.sum fun a _ => ContDiffAt.sum fun b _ => (component_diff hk a b).mul
        ((contDiffAt_pi.mp hshift a).mul (contDiffAt_pi.mp hshift b))))

lemma sourceOriginalEta_regular {f : SourceTensorFields} {y : Point}
    (hf : f.RegularAt y) (hy : y 0 ≠ 0) (hp : (sourceMetric f.base y).PosDef) (a : A) :
    ContDiffAt ℝ 2 (fun z => sourceOriginalEta f z a) y := by
  have h0 : determinant (sourceGamma f.base y) ≠ 0 := by
    rw [determinant_eq]
    exact (CKSAngularGeometry.metricBlock_leaf_posDef hp).det_pos.ne'
  have hs : 0 < sourceSchur f.base y := CKSAngularGeometry.metricBlock_schur_positive hp
  have hshift := (sourceShift_regular hf.base hy h0).of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have hk := sourceTangentialK_regular hf.base hy
  have hU : ContDiffAt ℝ 2 (fun z => 1/Real.sqrt (sourceSchur f.base z)) y :=
    contDiffAt_const.fun_div ((sourceSchur_regular hf.base hy h0).sqrt hs.ne') (Real.sqrt_ne_zero'.mpr hs)
  exact hU.mul ((contDiffAt_pi.mp hf.kb a).sub
    (ContDiffAt.sum fun b _ => (contDiffAt_pi.mp hshift b).mul (component_diff hk b a)))

lemma sourceOriginalTau_regular {f : SourceTensorFields} {y : Point}
    (hf : f.RegularAt y) (hy : y 0 ≠ 0) (hp : (sourceMetric f.base y).PosDef) :
    ContDiffAt ℝ 2 (sourceOriginalTau f) y := by
  have h0 : determinant (sourceGamma f.base y) ≠ 0 := by
    rw [determinant_eq]
    exact (CKSAngularGeometry.metricBlock_leaf_posDef hp).det_pos.ne'
  have hq := (sourceGamma_regular hf.base hy).of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have hk := sourceTangentialK_regular hf.base hy
  have hi := inverse_diff_at hq h0
  exact hk.sub (((traceProduct_diff hi hk).div_const 2).smul hq)

end
end CKSMixedGeometry

end

end OAI
