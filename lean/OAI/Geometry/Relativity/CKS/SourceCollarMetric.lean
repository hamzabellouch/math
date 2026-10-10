import OAI.Geometry.Relativity.CKS.SourceCollarBound
import OAI.Geometry.Relativity.CKS.CollarMetricRealization

namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter Matrix CKSAngularSlice
open CKSAngularGeometry (determinant determinant_eq)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

theorem cks_actual_collar_metric {K : Set MatrixThreeJet} (hK : IsCompact K)
    (hreg : ∀ q ∈ K, Matrix.PosDef (fun i k => (q i k).1.1))
    {B : ℝ} (hB : 0 ≤ B) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ (R : ℝ) (f : TensorFields) (ρ : ℝ) (x : AP),
      R₀ ≤ R → R ≤ Real.exp ρ → Real.exp ρ ≤ 3*R → f.RegularAt (slice ρ x) →
      ContDiffAt ℝ 3 f.base.mK (slice ρ x) → ContDiffAt ℝ 3 f.base.ek (slice ρ x) →
      (∀ᶠ y in 𝓝 (slice ρ x), (logMetric f.base y).PosDef) →
      matrixThreeJets f.base.sigma (slice ρ x) ∈ K → f.LogComponentBound B (slice ρ x) →
      ‖CKSAngularGeometry.fieldNormalizedMetric (CKSBending.collarParams R (Real.exp ρ))
        ((sourceCollarData f).angular ρ) x-
          CKSAngularGeometry.metricBlock 1 0 (f.base.sigma (slice ρ x))‖ ≤ C/(Real.exp ρ)^3 := by
  have hd (q) (hq : q ∈ K) : determinant (fun i k => (q i k).1.1) ≠ 0 := by
    exact (CKSAngularGeometry.determinant_eq (fun i k => (q i k).1.1)).symm ▸ (hreg q hq).det_pos.ne'
  obtain ⟨A,hA,hparams⟩ := CKSBending.collarParams_weighted
  obtain ⟨Rc,hRc,Cc,hCc,hcoeff⟩ := cks_sourceCollarData_bounded hK hd hB
  let L := restrictMatrixThree '' K
  have hL : IsCompact L := hK.image restrictMatrixThree_continuous
  have hregL : ∀ q ∈ L, determinant (fun i k => (q i k).1) ≠ 0 := by
    rintro _ ⟨q,hq,rfl⟩
    exact hd q hq
  let T := max A (2*Cc)
  have hT : 0 ≤ T := zero_le_one.trans (hA.trans (le_max_left _ _))
  obtain ⟨S,hS,C,hC,hmetric⟩ := CKSAngularGeometry.bounded_thin_collar_metric hL hregL hT
  refine ⟨max Rc S,hRc.trans (le_max_left _ _),C,hC,?_⟩
  intro R f ρ x hR hr htop hf hmk hek hp hs hb
  have hrRc : Rc ≤ Real.exp ρ := (le_max_left _ _).trans (hR.trans hr)
  have hrS : S ≤ Real.exp ρ := (le_max_right _ _).trans (hR.trans hr)
  have hsd : determinant (f.base.sigma (slice ρ x)) ≠ 0 := hd _ hs
  have hsource := sourceCollarData_regular hf hp hsd
  have hfield := angular_regular hsource (logTError_three_diff hf.base hmk hek hp.self_of_nhds)
  have hbound := hcoeff f (slice ρ x) (by simpa only [slice_zero] using hrRc) hf hp hs hb
  have hthin := angular_thin_bounded hCc (hRc.trans hrRc) hsource hbound
  have hmem : CKSAngularGeometry.matrixScalarJets (((sourceCollarData f).angular ρ).metric 0) x ∈ L := by
    change CKSAngularGeometry.matrixScalarJets (fun y => f.base.sigma (slice ρ y)) x ∈ L
    rw [sigma_slice_jets hf.base.sigma]
    exact ⟨_,hs,rfl⟩
  obtain ⟨_,hpbound⟩ := hparams R (Real.exp ρ) ((hRc.trans (le_max_left _ _)).trans hR) hr htop
  exact hmetric _ _ x hfield hmem (hpbound.trans (le_max_left _ _))
    (hthin.mono (le_max_right _ _)) (Real.exp ρ) hrS rfl

theorem source_actual_collar_metric {K : Set MatrixThreeJet} (hK : IsCompact K)
    (hreg : ∀ q ∈ K, Matrix.PosDef (fun i k => (q i k).1.1))
    {B : ℝ} (hB : 0 ≤ B) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ (R : ℝ) (f : SourceTensorFields) (ρ : ℝ) (x : AP),
      R₀ ≤ R → R ≤ Real.exp ρ → Real.exp ρ ≤ 3*R →
      f.RegularAt (logRadiusChart (slice ρ x)) →
      ContDiffAt ℝ 3 f.base.mK (angularProjection (logRadiusChart (slice ρ x))) →
      ContDiffAt ℝ 3 f.base.ek (logRadiusChart (slice ρ x)) →
      (∀ᶠ y in 𝓝 (logRadiusChart (slice ρ x)), (sourceMetric f.base y).PosDef) →
      matrixThreeJets (angularLift f.base.sigma) (slice ρ x) ∈ K →
      ‖matrixThreeJets (angularLift f.base.sigma) (slice ρ x)‖ ≤ B →
      ‖matrixThreeJets (angularLift f.base.mg) (slice ρ x)‖ ≤ B →
      ‖matrixScalarJets (angularLift f.base.mK) (slice ρ x)‖ ≤ B →
      ‖actualScalarJet (angularLift f.base.mr) (slice ρ x)‖ ≤ B →
      f.ComponentBounds B (logRadiusChart (slice ρ x)) →
      ‖CKSAngularGeometry.fieldNormalizedMetric (CKSBending.collarParams R (Real.exp ρ))
        ((sourceCollarData f.logFields).angular ρ) x-
          CKSAngularGeometry.metricBlock 1 0 (f.logFields.base.sigma (slice ρ x))‖ ≤ C/(Real.exp ρ)^3 := by
  obtain ⟨R₀,hR₀,C,hC,hh⟩ := cks_actual_collar_metric hK hreg hB
  refine ⟨R₀,hR₀,C,hC,?_⟩
  intro R f ρ x hR hr htop hf hmk hek hp hσ hs hmg hmK hmr hb
  have hmk' := hmk
  rw [angularProjection_logRadiusChart] at hmk'
  have hcl := (logRadiusChart_smooth.contDiffAt (x := slice ρ x)).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)
  exact hh R f.logFields ρ x hR hr htop (source_tensor_log_regular hf)
    (angularLift_diff hmk') (hek.comp _ hcl) (source_tensor_log_positive hp) hσ
    (source_tensor_log_bounds hB hf hs hmg hmK hmr hb)

end
end CKSMixedGeometry

end

end OAI
