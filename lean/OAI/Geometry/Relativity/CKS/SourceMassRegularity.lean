import OAI.Geometry.Relativity.CKS.CKSSourceMass

namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter Matrix
open CKSAngularGeometry (determinant inverse determinant_eq)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma sourceTangentialK_regular {f : SourceMassFields} {y : Point} (hf : f.RegularAt y) (hy : y 0 ≠ 0) :
    ContDiffAt ℝ 2 (sourceTangentialK f) y := by
  have hr : ContDiffAt ℝ 2 (fun z : Point => z 0) y := by fun_prop
  exact (((hr.pow 2).smul (angularLift_diff (hf.sigma.of_le (by norm_num)))).add
      ((contDiffAt_const.fun_div hr hy).smul (angularLift_diff hf.mK))).add hf.ek

lemma sourceRadialMetric_regular {f : SourceMassFields} {y : Point} (hf : f.RegularAt y) (hy : y 0 ≠ 0) :
    ContDiffAt ℝ 2 (sourceRadialMetric f) y := by
  have hr : ContDiffAt ℝ 2 (fun z : Point => z 0) y := by fun_prop
  exact ((contDiffAt_const.fun_div (contDiffAt_const.add (hr.pow 2)) (by positivity)).add
    ((angularLift_diff hf.mr).fun_div (hr.pow 5) (pow_ne_zero 5 hy))).add hf.err

lemma sourceSchur_regular {f : SourceMassFields} {y : Point} (hf : f.RegularAt y) (hy : y 0 ≠ 0)
    (h0 : determinant (sourceGamma f y) ≠ 0) : ContDiffAt ℝ 2 (sourceSchur f) y := by
  have hi := inverse_diff_at ((sourceGamma_regular hf hy).of_le (by norm_num : (2:ℕ∞ω) ≤ 3)) h0
  have hb := hf.b.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  exact (sourceRadialMetric_regular hf hy).sub (ContDiffAt.sum fun i _ => ContDiffAt.sum fun k _ =>
    (component_diff hi i k).mul ((contDiffAt_pi.mp hb i).mul (contDiffAt_pi.mp hb k)))

lemma sourceExpansion_regular {f : SourceMassFields} {y : Point} (hf : f.RegularAt y) (hy : y 0 ≠ 0)
    (h0 : determinant (sourceGamma f y) ≠ 0) : ContDiffAt ℝ 2 (sourceExpansion f) y := by
  have hq := sourceGamma_regular hf hy
  have hS := sourceShift_regular hf hy h0
  have hi := inverse_diff_at (hq.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)) h0
  have hqr := radialMatrixD_regular hq
  have hLie : ContDiffAt ℝ 2 (fun z => (show Mat from normalizedLie (sourceGamma f) (sourceShift f) z)) y := by
    exact contDiffAt_pi.mpr fun i => contDiffAt_pi.mpr fun k => normalizedLie_diff hq hS i k
  have hr : ContDiffAt ℝ 2 (fun z : Point => z 0/4) y := by fun_prop
  exact hr.mul (traceProduct_diff hi (hqr.sub hLie))

lemma sourcePhysicalMass_regular {f : SourceMassFields} {y : Point} (hf : f.RegularAt y) (hy : y 0 ≠ 0)
    (hp : (sourceMetric f y).PosDef) : ContDiffAt ℝ 2 (sourcePhysicalMass f) y := by
  have h0 : determinant (sourceGamma f y) ≠ 0 := by
    rw [determinant_eq]
    exact (CKSAngularGeometry.metricBlock_leaf_posDef hp).det_pos.ne'
  have hs : 0 < sourceSchur f y := CKSAngularGeometry.metricBlock_schur_positive hp
  have hi := inverse_diff_at ((sourceGamma_regular hf hy).of_le (by norm_num : (2:ℕ∞ω) ≤ 3)) h0
  have ht := traceProduct_diff hi (sourceTangentialK_regular hf hy)
  have hr : ContDiffAt ℝ 2 (fun z : Point => z 0/2) y := by fun_prop
  have hU : ContDiffAt ℝ 2 (fun z => 1/Real.sqrt (sourceSchur f z)) y :=
    contDiffAt_const.fun_div ((sourceSchur_regular hf hy h0).sqrt hs.ne')
    (Real.sqrt_ne_zero'.mpr hs)
  exact hr.mul ((contDiffAt_const.add ((hr.mul ht).pow 2)).sub
    ((hU.mul (sourceExpansion_regular hf hy h0)).pow 2))

lemma sourceAspect_regular {f : SourceMassFields} {y : Point} (hf : f.RegularAt y)
    (hσ : determinant (f.sigma (angularProjection y)) ≠ 0) :
    ContDiffAt ℝ 2 (angularLift (sourceAspect f)) y := by
  have hs := angularLift_diff (hf.sigma.of_le (by norm_num : (2:ℕ∞ω) ≤ 3))
  have hm := angularLift_diff (hf.mg.of_le (by norm_num : (2:ℕ∞ω) ≤ 3))
  have hk := angularLift_diff hf.mK
  have hi := inverse_diff_at (x := y) hs hσ
  exact (traceProduct_diff hi (hm.add (hk.const_smul (2:ℝ)))).add
    ((angularLift_diff hf.mr).const_smul (2:ℝ))

end
end CKSMixedGeometry

end

end OAI
