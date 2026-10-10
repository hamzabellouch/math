import OAI.Geometry.Relativity.CKS.LogPhysicalTensor
import OAI.Geometry.Relativity.CKS.CKSTensorCompact
import OAI.Geometry.Relativity.CKS.CKSTensorRealization
import OAI.Geometry.Relativity.CKS.LogPhysicalMassJet

namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter Matrix
open CKSAngularGeometry (determinant determinant_eq)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma normalizeTensorLogFields_regular {f : TensorFields} {x : Point} (hf : f.RegularAt x) :
    (normalizeTensorLogFields f).RegularAt x := by
  exact ⟨normalizeMassLogFields_regular hf.base,(radiusPower_diff 5 2 x).mul hf.kr,
    (radiusPower_diff 3 2 x).smul hf.kb⟩

lemma normalize_tensor_kr_bound {f : TensorFields} {x : Point} {B : ℝ}
    (hf : f.RegularAt x) (h : ‖actualScalarJet f.kr x‖ ≤ B/Real.exp (x 0)^5) :
    ‖actualScalarJet (normalizeTensorLogFields f).kr x‖ ≤ 100*B := by
  have hh := normalize_two_bound hf.kr h
  norm_num at hh
  exact hh

lemma normalize_tensor_kb_bound {f : TensorFields} {x : Point} {B : ℝ} (hB : 0 ≤ B)
    (hf : f.RegularAt x) (h : ‖fun a => actualScalarJet (fun y => f.kb y a) x‖ ≤ B/Real.exp (x 0)^3) :
    ‖fun a => actualScalarJet (fun y => (normalizeTensorLogFields f).kb y a) x‖ ≤ 36*B := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro a
  have hh := normalize_two_bound (contDiffAt_pi.mp hf.kb a) ((norm_le_pi_norm _ a).trans h)
  norm_num at hh
  exact hh

lemma tensorDenField_positive {f : TensorFields} {x : Point} (h : 0 < logSchur f.base x) :
    0 < tensorDenField (radiusPower (-1)) (normalizeTensorLogFields f) x := by
  change 0 < 1+radiusPower (-1) x^3*cksVField (radiusPower (-1)) (normalizeMassLogFields f.base) x
  rw [radiusPower_inverse,← log_schur_coefficient]
  positivity

lemma minus_three_product_bound {g : Point → ℝ} {x : Point} {C : ℝ}
    (hg : ContDiffAt ℝ 2 g x) (hC : ‖actualScalarJet g x‖ ≤ C) :
    ‖actualScalarJet (fun y => radiusPower (-3) y*g y) x‖ ≤ 36*C/Real.exp (x 0)^3 := by
  rw [actualScalarJet_mul (radiusPower_diff (-3) 2 x) hg]
  have hz : ‖actualScalarJet (radiusPower (-3)) x‖ ≤ 9/Real.exp (x 0)^3 := by
    have hh := radiusPower_two_norm (-3) x
    norm_num only [abs_neg,abs_of_pos (by norm_num : (0:ℝ) < 3),
      max_eq_right (by norm_num : (1:ℝ) ≤ 3),radiusPower_minus_three] at hh
    norm_num at hh
    exact hh
  exact (productJet_norm hz hC).trans_eq (by ring)

theorem cks_physical_tensor_mixed {K : Set MatrixThreeJet} (hK : IsCompact K)
    (hreg : ∀ q ∈ K, determinant (fun i k => (q i k).1.1) ≠ 0)
    {B : ℝ} (hB : 0 ≤ B) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ f : TensorFields, ∀ x : Point,
      R₀ ≤ Real.exp (x 0) → f.RegularAt x →
      (∀ᶠ y in 𝓝 x, (logMetric f.base y).PosDef) → matrixThreeJets f.base.sigma x ∈ K →
      ‖matrixThreeJets f.base.sigma x‖ ≤ B → ‖matrixThreeJets f.base.mg x‖ ≤ B →
      ‖matrixThreeJets f.base.eg x‖ ≤ B/Real.exp (x 0)^2 →
      ‖matrixScalarJets f.base.mK x‖ ≤ B → ‖matrixScalarJets f.base.ek x‖ ≤ B/Real.exp (x 0)^2 →
      ‖fun a => actualThreeJet (fun y => f.base.b y a) x‖ ≤ B/Real.exp (x 0)^3 →
      ‖actualScalarJet f.base.mr x‖ ≤ B → ‖actualScalarJet f.base.err x‖ ≤ B/Real.exp (x 0)^6 →
      ‖actualScalarJet f.kr x‖ ≤ B/Real.exp (x 0)^5 →
      ‖fun a => actualScalarJet (fun y => f.kb y a) x‖ ≤ B/Real.exp (x 0)^3 →
      ‖actualScalarJet (fun y => logOriginalL f y-1) x‖ ≤ C/Real.exp (x 0)^3 ∧
      (∀ a, ‖actualScalarJet (fun y => logOriginalEta f y a/Real.exp (y 0)) x‖ ≤ C/Real.exp (x 0)^3) ∧
      (∀ a b, ‖actualScalarJet (fun y => logOriginalTau f y a b/Real.exp (y 0)^2) x‖ ≤ C/Real.exp (x 0)^3) := by
  obtain ⟨R,hR,C,hC,hh⟩ := cks_tensor_coefficients_bounded hK hreg (216*B)
  refine ⟨R,hR,36*C,by positivity,?_⟩
  intro f x hr hf hp hσ hs hmg heg hmk hek hb hmr herr hkr hkb
  have hn := normalizeTensorLogFields_regular hf
  have hz := radiusPower_diff (-1) 3 x
  obtain ⟨hq,hS⟩ := logMetric_normalized_positive hp.self_of_nhds
  have h0 : determinant (cksQField (radiusPower (-1)) (normalizeTensorLogFields f).base x) ≠ 0 := by
    rw [determinant_eq]
    exact hq.det_pos.ne'
  have hden := tensorDenField_positive (f := f) hS
  have hnB := normalized_log_mass_input_bound hB hf.base hs hmg heg hmk hek hb hmr herr
  have hnkr : ‖actualScalarJet (normalizeTensorLogFields f).kr x‖ ≤ 216*B :=
    (normalize_tensor_kr_bound hf hkr).trans (by linarith)
  have hnkb : ‖fun a => actualScalarJet (fun y => (normalizeTensorLogFields f).kb y a) x‖ ≤ 216*B :=
    (normalize_tensor_kb_bound hB hf hkb).trans (by linarith)
  have ht := hh (Real.exp (x 0)) (actualThreeJet (radiusPower (-1)) x)
    (tensorInputOf (normalizeTensorLogFields f) x) hr (inverse_radius_three_norm x) hσ hnB hnkr hnkb
  obtain ⟨hL,hET⟩ := norm_prod_le_iff.mp ht
  obtain ⟨hE,hT⟩ := norm_prod_le_iff.mp hET
  have hL' : ‖actualScalarJet (tensorLField (radiusPower (-1)) (normalizeTensorLogFields f)) x‖ ≤ C := by
    rw [actual_tensorL hz hn h0 hden]
    exact hL
  have hE' (a : A) : ‖actualScalarJet (fun y => tensorEtaField (radiusPower (-1)) (normalizeTensorLogFields f) y a) x‖ ≤ C := by
    rw [actual_tensorEta hz hn h0 hden]
    exact (norm_le_pi_norm _ a).trans hE
  have hT' (a b : A) : ‖actualScalarJet (fun y => tensorTauField (radiusPower (-1)) (normalizeTensorLogFields f) y a b) x‖ ≤ C := by
    have hm := actual_tensorTau hz hn h0
    have hab := congrFun (congrFun hm a) b
    rw [show actualScalarJet (fun y => tensorTauField (radiusPower (-1)) (normalizeTensorLogFields f) y a b) x = _ from hab]
    exact (norm_le_pi_norm _ b).trans ((norm_le_pi_norm _ a).trans hT)
  have hSnear : ∀ᶠ y in 𝓝 x, 0 < logSchur f.base y := by
    filter_upwards [hp] with y hy using (logMetric_normalized_positive hy).2
  refine ⟨?_,?_,?_⟩
  · have heq : actualScalarJet (fun y => logOriginalL f y-1) x =
        actualScalarJet (fun y => radiusPower (-3) y*tensorLField (radiusPower (-1)) (normalizeTensorLogFields f) y) x := by
      apply actualScalarJet_congr
      filter_upwards [hSnear] with y hy using logOriginalL_normalized hy
    rw [heq]
    exact minus_three_product_bound (tensorLField_diff hz hn h0 hden) hL'
  · intro a
    have heq : actualScalarJet (fun y => logOriginalEta f y a/Real.exp (y 0)) x =
        actualScalarJet (fun y => radiusPower (-3) y*tensorEtaField (radiusPower (-1)) (normalizeTensorLogFields f) y a) x := by
      apply actualScalarJet_congr
      filter_upwards [hSnear] with y hy using logOriginalEta_normalized hy a
    rw [heq]
    exact minus_three_product_bound (tensorEtaField_diff hz hn h0 hden a) (hE' a)
  · intro a b
    have heq : actualScalarJet (fun y => logOriginalTau f y a b/Real.exp (y 0)^2) x =
        actualScalarJet (fun y => radiusPower (-3) y*tensorTauField (radiusPower (-1)) (normalizeTensorLogFields f) y a b) x := by
      apply actualScalarJet_congr
      filter_upwards [hp] with y hy
      have hd : determinant (cksQField (radiusPower (-1)) (normalizeMassLogFields f.base) y) ≠ 0 := by
        rw [determinant_eq]
        exact (logMetric_normalized_positive hy).1.det_pos.ne'
      have h := congrFun (congrFun (logOriginalTau_normalized hd) a) b
      change (Real.exp (y 0)^2)⁻¹*logOriginalTau f y a b = radiusPower (-3) y*
        tensorTauField (radiusPower (-1)) (normalizeTensorLogFields f) y a b at h
      simpa only [div_eq_mul_inv,mul_comm] using h
    rw [heq]
    exact minus_three_product_bound (component_diff (tensorTauField_diff hz hn h0) a b) (hT' a b)

end
end CKSMixedGeometry

end

end OAI
