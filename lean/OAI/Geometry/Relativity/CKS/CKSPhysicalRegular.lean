import OAI.Geometry.Relativity.CKS.LogPhysicalFoliation
import OAI.Geometry.Relativity.CKS.CKSTensorMixed

namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter Matrix
open CKSAngularGeometry (determinant determinant_eq)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma cksLeadingField_diff {f : MassFields} {x : Point} (hf : f.RegularAt x)
    (hσ : determinant (f.sigma x) ≠ 0) : ContDiffAt ℝ 2 (cksLeadingField f) x := by
  have hs := inverse_diff_at (hf.sigma.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)) hσ
  exact ((hf.mr.const_smul (1/2:ℝ)).add
    ((traceProduct_diff hs (hf.mg.of_le (by norm_num))).const_smul (1/4:ℝ))).add
    ((traceProduct_diff hs hf.mK).const_smul (1/2:ℝ))

lemma cksFField_diff {z : Point → ℝ} {f : MassFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x)
    (hq : determinant (cksQField z f x) ≠ 0)
    (hV : 1+z x^3*cksVField z f x ≠ 0) : ContDiffAt ℝ 2 (cksFField z f) x := by
  have hz2 := hz.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have hd := cksDField_diff hz hf hq
  have ht := cksTField_diff hz hf hq
  have hv := cksVField_diff hz hf hq
  exact ((massNumeratorField_diff hz2 hd ht hv).mul
    ((contDiffAt_const.add ((hz2.pow 3).mul hv)).inv hV)).const_smul (1/2:ℝ)

lemma logPhysicalMass_diff {f : MassFields} {x : Point}
    (hf : f.RegularAt x) (hp : ∀ᶠ y in 𝓝 x, (logMetric f y).PosDef) :
    ContDiffAt ℝ 2 (logPhysicalMass f) x := by
  obtain ⟨hq,hs⟩ := logMetric_normalized_positive hp.self_of_nhds
  have hd : determinant (cksQField (radiusPower (-1)) (normalizeMassLogFields f) x) ≠ 0 := by
    rw [determinant_eq]; exact hq.det_pos.ne'
  have hV : 1+radiusPower (-1) x^3*cksVField (radiusPower (-1)) (normalizeMassLogFields f) x ≠ 0 := by
    rw [radiusPower_inverse,← log_schur_coefficient]
    positivity
  apply (cksFField_diff (radiusPower_diff (-1) 3 x) (normalizeMassLogFields_regular hf) hd hV).congr_of_eventuallyEq
  filter_upwards [hf.eventually,hp] with y hy hpy
  obtain ⟨hq,hs⟩ := logMetric_normalized_positive hpy
  have hd : determinant (cksQField (radiusPower (-1)) (normalizeMassLogFields f) y) ≠ 0 := by
    rw [determinant_eq]; exact hq.det_pos.ne'
  exact log_physical_mass_eq hy hd hs

lemma logShift_diff {f : MassFields} {x : Point} (hf : f.RegularAt x)
    (hp : (logMetric f x).PosDef) : ContDiffAt ℝ 3 (logShift f) x := by
  have hd : determinant (cksQField (radiusPower (-1)) (normalizeMassLogFields f) x) ≠ 0 := by
    rw [determinant_eq]; exact (logMetric_normalized_positive hp).1.det_pos.ne'
  rw [logShift_normalized]
  exact (radiusPower_diff (-5) 3 x).smul
    (cksHField_diff (radiusPower_diff (-1) 3 x) (normalizeMassLogFields_regular hf) hd)

lemma logTError_diff {f : MassFields} {x : Point} (hf : f.RegularAt x)
    (hp : ∀ᶠ y in 𝓝 x, (logMetric f y).PosDef) :
    ContDiffAt ℝ 2 (fun y => logT f y-1) x := by
  have hd : determinant (cksQField (radiusPower (-1)) (normalizeMassLogFields f) x) ≠ 0 := by
    rw [determinant_eq]; exact (logMetric_normalized_positive hp.self_of_nhds).1.det_pos.ne'
  apply ((radiusPower_diff (-3) 2 x).mul
    (cksTField_diff (radiusPower_diff (-1) 3 x) (normalizeMassLogFields_regular hf) hd)).congr_of_eventuallyEq
  filter_upwards [hp] with y hy
  have hd : determinant (cksQField (radiusPower (-1)) (normalizeMassLogFields f) y) ≠ 0 := by
    rw [determinant_eq]; exact (logMetric_normalized_positive hy).1.det_pos.ne'
  unfold logT
  rw [log_trace_coefficient hd,radiusPower_minus_three]
  ring

lemma logOriginalLError_diff {f : TensorFields} {x : Point} (hf : f.RegularAt x)
    (hp : ∀ᶠ y in 𝓝 x, (logMetric f.base y).PosDef) :
    ContDiffAt ℝ 2 (fun y => logOriginalL f y-1) x := by
  obtain ⟨hq,hs⟩ := logMetric_normalized_positive hp.self_of_nhds
  have hd : determinant (cksQField (radiusPower (-1)) (normalizeTensorLogFields f).base x) ≠ 0 := by
    rw [determinant_eq]; exact hq.det_pos.ne'
  apply ((radiusPower_diff (-3) 2 x).mul
    (tensorLField_diff (radiusPower_diff (-1) 3 x) (normalizeTensorLogFields_regular hf) hd
      (tensorDenField_positive hs))).congr_of_eventuallyEq
  filter_upwards [hp] with y hy using logOriginalL_normalized (logMetric_normalized_positive hy).2

lemma logOriginalEtaDiv_diff {f : TensorFields} {x : Point} (hf : f.RegularAt x)
    (hp : ∀ᶠ y in 𝓝 x, (logMetric f.base y).PosDef) :
    ContDiffAt ℝ 2 (fun y a => logOriginalEta f y a/Real.exp (y 0)) x := by
  obtain ⟨hq,hs⟩ := logMetric_normalized_positive hp.self_of_nhds
  have hd : determinant (cksQField (radiusPower (-1)) (normalizeTensorLogFields f).base x) ≠ 0 := by
    rw [determinant_eq]; exact hq.det_pos.ne'
  apply contDiffAt_pi.mpr; intro a
  apply ((radiusPower_diff (-3) 2 x).mul
    (tensorEtaField_diff (radiusPower_diff (-1) 3 x) (normalizeTensorLogFields_regular hf) hd
      (tensorDenField_positive hs) a)).congr_of_eventuallyEq
  filter_upwards [hp] with y hy using logOriginalEta_normalized (logMetric_normalized_positive hy).2 a

lemma logOriginalTauDiv_diff {f : TensorFields} {x : Point} (hf : f.RegularAt x)
    (hp : ∀ᶠ y in 𝓝 x, (logMetric f.base y).PosDef) :
    ContDiffAt ℝ 2 (fun y a b => logOriginalTau f y a b/Real.exp (y 0)^2) x := by
  have hd : determinant (cksQField (radiusPower (-1)) (normalizeTensorLogFields f).base x) ≠ 0 := by
    rw [determinant_eq]; exact (logMetric_normalized_positive hp.self_of_nhds).1.det_pos.ne'
  apply contDiffAt_pi.mpr; intro a; apply contDiffAt_pi.mpr; intro b
  apply ((radiusPower_diff (-3) 2 x).mul
    (component_diff (tensorTauField_diff (radiusPower_diff (-1) 3 x)
      (normalizeTensorLogFields_regular hf) hd) a b)).congr_of_eventuallyEq
  filter_upwards [hp] with y hy
  have hd : determinant (cksQField (radiusPower (-1)) (normalizeMassLogFields f.base) y) ≠ 0 := by
    rw [determinant_eq]; exact (logMetric_normalized_positive hy).1.det_pos.ne'
  have hh := congrFun (congrFun (logOriginalTau_normalized hd) a) b
  change (Real.exp (y 0)^2)⁻¹*logOriginalTau f y a b =
    radiusPower (-3) y*tensorTauField (radiusPower (-1)) (normalizeTensorLogFields f) y a b at hh
  simpa only [div_eq_mul_inv,mul_comm] using hh

end
end CKSMixedGeometry

end

end OAI
