import OAI.Geometry.Relativity.CKS.LogPhysicalFoliation
import OAI.Geometry.Relativity.CKS.CKSTensorMixed
import OAI.Geometry.Relativity.CKS.CKSFoliationLeadingFields
import OAI.Geometry.Relativity.CKS.CKSSourceMass

namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter Matrix
open CKSAngularGeometry (determinant determinant_eq)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

attribute [local irreducible] coefficientD coefficientT coefficientShift lapseCorrection uCorrection

theorem cks_physical_foliation_asymptotics {K : Set MatrixThreeJet} (hK : IsCompact K)
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
      ‖actualScalarJet (fun y => logExpansion f y-1-radiusPower (-3) y*leadingDField f y) x‖ ≤ C/Real.exp (x 0)^4 ∧
      ‖actualScalarJet (fun y => logT f y-1-radiusPower (-3) y*leadingTField f y) x‖ ≤ C/Real.exp (x 0)^4 ∧
      ‖actualScalarJet (fun y => logLapse f y/Real.sqrt (1+Real.exp (y 0)^2)-1-radiusPower (-3) y*leadingLapseField f y) x‖ ≤ C/Real.exp (x 0)^4 ∧
      ‖actualScalarJet (fun y => logU f y/Real.sqrt (1+Real.exp (y 0)^2)-1-radiusPower (-3) y*leadingUField f y) x‖ ≤ C/Real.exp (x 0)^4 := by
  obtain ⟨R,hR,C,hC,hh⟩ := cks_foliation_leading_bounded hK hreg (216*B)
  refine ⟨R,hR,36*C,by positivity,?_⟩
  intro f x hr hf hp hσ hs hmg heg hmk hek hb hmr herr
  have hn := normalizeMassLogFields_regular hf
  have hz := radiusPower_diff (-1) 3 x
  have hσ0 : determinant (f.sigma x) ≠ 0 := hreg _ hσ
  obtain ⟨hq,hS⟩ := logMetric_normalized_positive hp.self_of_nhds
  have h0 : determinant (cksQField (radiusPower (-1)) (normalizeMassLogFields f) x) ≠ 0 := by
    rw [determinant_eq]
    exact hq.det_pos.ne'
  have hden := foliationDenField_positive (f := f) hS
  have hnB := normalized_log_mass_input_bound hB hf hs hmg heg hmk hek hb hmr herr
  obtain ⟨hD,hT,hL,hW⟩ := hh (Real.exp (x 0)) (actualThreeJet (radiusPower (-1)) x)
    (massInputOf (normalizeMassLogFields f) x) hr (inverse_radius_three_norm x) hσ hnB
  have hD' : ‖actualScalarJet (fun y => cksDField (radiusPower (-1)) (normalizeMassLogFields f) y-leadingDField f y) x‖ ≤ C/Real.exp (x 0) := by
    rw [actualScalarJet_sub (cksDField_diff hz hn h0) (leadingDField_diff hf hσ0),cksDField_realized hz hn h0,leadingDField_realized hf hσ0]
    exact hD
  have hT' : ‖actualScalarJet (fun y => cksTField (radiusPower (-1)) (normalizeMassLogFields f) y-leadingTField f y) x‖ ≤ C/Real.exp (x 0) := by
    rw [actualScalarJet_sub (cksTField_diff hz hn h0) (leadingTField_diff hf hσ0),cksTField_realized hz hn h0,leadingTField_realized hf hσ0]
    exact hT
  have hL' : ‖actualScalarJet (fun y => lapseCorrectionField (radiusPower (-1)) (normalizeMassLogFields f) y-leadingLapseField f y) x‖ ≤ C/Real.exp (x 0) := by
    rw [actualScalarJet_sub (lapseCorrectionField_diff hz hn h0 hden) (leadingLapseField_diff hf),actual_lapseCorrection hz hn h0 hden,leadingLapseField_realized hf]
    exact hL
  have hW' : ‖actualScalarJet (fun y => uCorrectionField (radiusPower (-1)) (normalizeMassLogFields f) y-leadingUField f y) x‖ ≤ C/Real.exp (x 0) := by
    rw [actualScalarJet_sub (uCorrectionField_diff hz hn h0 hden) (leadingUField_diff hf hσ0),actual_uCorrection hz hn h0 hden,leadingUField_realized hf hσ0]
    exact hW
  have hsmall : 36*(C/Real.exp (x 0))/Real.exp (x 0)^3 = 36*C/Real.exp (x 0)^4 := by
    field_simp
  have hnear : ∀ᶠ y in 𝓝 x, determinant (cksQField (radiusPower (-1)) (normalizeMassLogFields f) y) ≠ 0 ∧
      0 < logSchur f y := by
    filter_upwards [hp] with y hy
    obtain ⟨hq,hs⟩ := logMetric_normalized_positive hy
    exact ⟨by rw [determinant_eq]; exact hq.det_pos.ne',hs⟩
  refine ⟨?_,?_,?_,?_⟩
  · have heq : actualScalarJet (fun y => logExpansion f y-1-radiusPower (-3) y*leadingDField f y) x =
        actualScalarJet (fun y => radiusPower (-3) y*(cksDField (radiusPower (-1)) (normalizeMassLogFields f) y-leadingDField f y)) x := by
      apply actualScalarJet_congr
      filter_upwards [hnear,hf.eventually] with y hy hfy
      rw [log_expansion_coefficient hfy hy.1,radiusPower_minus_three]
      ring
    rw [heq]
    exact (minus_three_product_bound ((cksDField_diff hz hn h0).sub (leadingDField_diff hf hσ0)) hD').trans_eq hsmall
  · have heq : actualScalarJet (fun y => logT f y-1-radiusPower (-3) y*leadingTField f y) x =
        actualScalarJet (fun y => radiusPower (-3) y*(cksTField (radiusPower (-1)) (normalizeMassLogFields f) y-leadingTField f y)) x := by
      apply actualScalarJet_congr
      filter_upwards [hnear] with y hy
      unfold logT
      rw [log_trace_coefficient hy.1,radiusPower_minus_three]
      ring
    rw [heq]
    exact (minus_three_product_bound ((cksTField_diff hz hn h0).sub (leadingTField_diff hf hσ0)) hT').trans_eq hsmall
  · have heq : actualScalarJet (fun y => logLapse f y/Real.sqrt (1+Real.exp (y 0)^2)-1-radiusPower (-3) y*leadingLapseField f y) x =
        actualScalarJet (fun y => radiusPower (-3) y*(lapseCorrectionField (radiusPower (-1)) (normalizeMassLogFields f) y-leadingLapseField f y)) x := by
      apply actualScalarJet_congr
      filter_upwards [hnear] with y hy
      rw [log_lapse_normalized hy.2]
      ring
    rw [heq]
    exact (minus_three_product_bound ((lapseCorrectionField_diff hz hn h0 hden).sub (leadingLapseField_diff hf)) hL').trans_eq hsmall
  · have heq : actualScalarJet (fun y => logU f y/Real.sqrt (1+Real.exp (y 0)^2)-1-radiusPower (-3) y*leadingUField f y) x =
        actualScalarJet (fun y => radiusPower (-3) y*(uCorrectionField (radiusPower (-1)) (normalizeMassLogFields f) y-leadingUField f y)) x := by
      apply actualScalarJet_congr
      filter_upwards [hnear,hf.eventually] with y hy hfy
      rw [log_u_normalized hfy hy.1 hy.2]
      ring
    rw [heq]
    exact (minus_three_product_bound ((uCorrectionField_diff hz hn h0 hden).sub (leadingUField_diff hf hσ0)) hW').trans_eq hsmall

end
end CKSMixedGeometry

end

end OAI
