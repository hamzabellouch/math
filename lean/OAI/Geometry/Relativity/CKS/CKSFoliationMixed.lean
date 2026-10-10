import OAI.Geometry.Relativity.CKS.LogPhysicalFoliation
import OAI.Geometry.Relativity.CKS.CKSTensorMixed

namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter Matrix
open CKSAngularGeometry (determinant determinant_eq)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma minus_five_product_bound {g : Point → ℝ} {x : Point} {C : ℝ}
    (hg : ContDiffAt ℝ 3 g x) (hC : ‖actualThreeJet g x‖ ≤ C) :
    ‖actualThreeJet (fun y => radiusPower (-5) y*g y) x‖ ≤ 1000*C/Real.exp (x 0)^5 := by
  rw [actualThreeJet_mul (radiusPower_diff (-5) 3 x) hg]
  have hz : ‖actualThreeJet (radiusPower (-5)) x‖ ≤ 125/Real.exp (x 0)^5 := by
    have hh := radiusPower_three_norm (-5) x
    norm_num only [abs_neg,abs_of_pos (by norm_num : (0:ℝ) < 5),
      max_eq_right (by norm_num : (1:ℝ) ≤ 5),radiusPower_minus_five] at hh
    norm_num at hh
    exact hh
  exact (productThreeJet_norm hz hC).trans_eq (by ring)

attribute [local irreducible] coefficientD coefficientT coefficientShift lapseCorrection uCorrection

theorem cks_physical_foliation_mixed {K : Set MatrixThreeJet} (hK : IsCompact K)
    (hreg : ∀ q ∈ K, determinant (fun i k => (q i k).1.1) ≠ 0)
    {B : ℝ} (hB : 0 ≤ B) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ f : MassFields, ∀ x : Point,
      R₀ ≤ Real.exp (x 0) → f.RegularAt x →
      (∀ᶠ y in 𝓝 x, (logMetric f y).PosDef) → matrixThreeJets f.sigma x ∈ K →
      ‖matrixThreeJets f.sigma x‖ ≤ B → ‖matrixThreeJets f.mg x‖ ≤ B →
      ‖matrixThreeJets f.eg x‖ ≤ B/Real.exp (x 0)^2 →
      ‖matrixScalarJets f.mK x‖ ≤ B → ‖matrixScalarJets f.ek x‖ ≤ B/Real.exp (x 0)^2 →
      ‖fun a => actualThreeJet (fun y => f.b y a) x‖ ≤ B/Real.exp (x 0)^3 →
      ‖actualScalarJet f.mr x‖ ≤ B → ‖actualScalarJet f.err x‖ ≤ B/Real.exp (x 0)^6 →
      ‖actualScalarJet (fun y => logExpansion f y-1) x‖ ≤ C/Real.exp (x 0)^3 ∧
      ‖actualScalarJet (fun y => logT f y-1) x‖ ≤ C/Real.exp (x 0)^3 ∧
      (∀ a, ‖actualThreeJet (fun y => logShift f y a) x‖ ≤ C/Real.exp (x 0)^5) ∧
      ‖actualScalarJet (fun y => logLapse f y/Real.sqrt (1+Real.exp (y 0)^2)-1) x‖ ≤ C/Real.exp (x 0)^3 ∧
      ‖actualScalarJet (fun y => logU f y/Real.sqrt (1+Real.exp (y 0)^2)-1) x‖ ≤ C/Real.exp (x 0)^3 := by
  obtain ⟨R,hR,C,hC,hh⟩ := cks_foliation_coefficients_bounded hK hreg (216*B)
  refine ⟨R,hR,1000*C,by positivity,?_⟩
  intro f x hr hf hp hσ hs hmg heg hmk hek hb hmr herr
  have hn := normalizeMassLogFields_regular hf
  have hz := radiusPower_diff (-1) 3 x
  obtain ⟨hq,hS⟩ := logMetric_normalized_positive hp.self_of_nhds
  have h0 : determinant (cksQField (radiusPower (-1)) (normalizeMassLogFields f) x) ≠ 0 := by
    rw [determinant_eq]
    exact hq.det_pos.ne'
  have hden := foliationDenField_positive (f := f) hS
  have hnB := normalized_log_mass_input_bound hB hf hs hmg heg hmk hek hb hmr herr
  have ht := hh (Real.exp (x 0)) (actualThreeJet (radiusPower (-1)) x)
    (massInputOf (normalizeMassLogFields f) x) hr (inverse_radius_three_norm x) hσ hnB
  simp only [foliationCoefficients] at ht
  obtain ⟨hD,hrest⟩ := norm_prod_le_iff.mp ht
  obtain ⟨hT,hrest⟩ := norm_prod_le_iff.mp hrest
  obtain ⟨hH,hrest⟩ := norm_prod_le_iff.mp hrest
  obtain ⟨hL,hW⟩ := norm_prod_le_iff.mp hrest
  have hD' : ‖actualScalarJet (cksDField (radiusPower (-1)) (normalizeMassLogFields f)) x‖ ≤ C := by
    rw [cksDField_realized hz hn h0]; exact hD
  have hT' : ‖actualScalarJet (cksTField (radiusPower (-1)) (normalizeMassLogFields f)) x‖ ≤ C := by
    rw [cksTField_realized hz hn h0]; exact hT
  have hH' (a : A) : ‖actualThreeJet (fun y => cksHField (radiusPower (-1)) (normalizeMassLogFields f) y a) x‖ ≤ C := by
    rw [congrFun (cksHField_realized hz hn h0) a]
    exact (norm_le_pi_norm _ a).trans hH
  have hL' : ‖actualScalarJet (lapseCorrectionField (radiusPower (-1)) (normalizeMassLogFields f)) x‖ ≤ C := by
    rw [actual_lapseCorrection hz hn h0 hden]; exact hL
  have hW' : ‖actualScalarJet (uCorrectionField (radiusPower (-1)) (normalizeMassLogFields f)) x‖ ≤ C := by
    rw [actual_uCorrection hz hn h0 hden]; exact hW
  have hsmall : 36*C/Real.exp (x 0)^3 ≤ 1000*C/Real.exp (x 0)^3 :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  have hnear : ∀ᶠ y in 𝓝 x, determinant (cksQField (radiusPower (-1)) (normalizeMassLogFields f) y) ≠ 0 ∧
      0 < logSchur f y := by
    filter_upwards [hp] with y hy
    obtain ⟨hq,hs⟩ := logMetric_normalized_positive hy
    exact ⟨by rw [determinant_eq]; exact hq.det_pos.ne',hs⟩
  refine ⟨?_,?_,?_,?_,?_⟩
  · have heq : actualScalarJet (fun y => logExpansion f y-1) x =
        actualScalarJet (fun y => radiusPower (-3) y*cksDField (radiusPower (-1)) (normalizeMassLogFields f) y) x := by
      apply actualScalarJet_congr
      filter_upwards [hnear,hf.eventually] with y hy hfy
      rw [log_expansion_coefficient hfy hy.1,radiusPower_minus_three]
      ring
    rw [heq]
    exact (minus_three_product_bound (cksDField_diff hz hn h0) hD').trans hsmall
  · have heq : actualScalarJet (fun y => logT f y-1) x =
        actualScalarJet (fun y => radiusPower (-3) y*cksTField (radiusPower (-1)) (normalizeMassLogFields f) y) x := by
      apply actualScalarJet_congr
      filter_upwards [hnear] with y hy
      unfold logT
      rw [log_trace_coefficient hy.1,radiusPower_minus_three]
      ring
    rw [heq]
    exact (minus_three_product_bound (cksTField_diff hz hn h0) hT').trans hsmall
  · intro a
    have heq : (fun y => logShift f y a) = fun y =>
        radiusPower (-5) y*cksHField (radiusPower (-1)) (normalizeMassLogFields f) y a := by
      rw [logShift_normalized]; rfl
    rw [heq]
    exact minus_five_product_bound (contDiffAt_pi.mp (cksHField_diff hz hn h0) a) (hH' a)
  · have heq : actualScalarJet (fun y => logLapse f y/Real.sqrt (1+Real.exp (y 0)^2)-1) x =
        actualScalarJet (fun y => radiusPower (-3) y*lapseCorrectionField (radiusPower (-1)) (normalizeMassLogFields f) y) x := by
      apply actualScalarJet_congr
      filter_upwards [hnear] with y hy using log_lapse_normalized hy.2
    rw [heq]
    exact (minus_three_product_bound (lapseCorrectionField_diff hz hn h0 hden) hL').trans hsmall
  · have heq : actualScalarJet (fun y => logU f y/Real.sqrt (1+Real.exp (y 0)^2)-1) x =
        actualScalarJet (fun y => radiusPower (-3) y*uCorrectionField (radiusPower (-1)) (normalizeMassLogFields f) y) x := by
      apply actualScalarJet_congr
      filter_upwards [hnear,hf.eventually] with y hy hfy using log_u_normalized hfy hy.1 hy.2
    rw [heq]
    exact (minus_three_product_bound (uCorrectionField_diff hz hn h0 hden) hW').trans hsmall

end
end CKSMixedGeometry

end

end OAI
