import OAI.Geometry.Relativity.CKS.CKSCollarConcrete
import OAI.Geometry.Relativity.CKS.SourcePhysicalTensor

namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter Matrix CKSAngularSlice
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma source_tensor_log_bounds {f : SourceTensorFields} {x : Point} {B : ℝ}
    (hB : 0 ≤ B) (hf : f.RegularAt (logRadiusChart x))
    (hσ : ‖matrixThreeJets (angularLift f.base.sigma) x‖ ≤ B)
    (hmg : ‖matrixThreeJets (angularLift f.base.mg) x‖ ≤ B)
    (hmk : ‖matrixScalarJets (angularLift f.base.mK) x‖ ≤ B)
    (hmr : ‖actualScalarJet (angularLift f.base.mr) x‖ ≤ B)
    (hb : f.ComponentBounds B (logRadiusChart x)) : f.logFields.LogComponentBound B x := by
  obtain ⟨heg,hek,hb',herr⟩ := source_log_remainder_bounds hB hf.base hb.base
  refine ⟨hσ,hmg,heg,hmk,hek,hb',hmr,herr,
    source_two_jet_bound hB hf.kr hb.kr,?_⟩
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro a
  exact source_two_jet_bound hB (contDiffAt_pi.mp hf.kb a) (hb.kb a)

lemma source_tensor_log_positive {f : SourceTensorFields} {x : Point}
    (hp : ∀ᶠ y in 𝓝 (logRadiusChart x), (sourceMetric f.base y).PosDef) :
    ∀ᶠ y in 𝓝 x, (logMetric f.logFields.base y).PosDef := by
  have hc := logRadiusChart_smooth.continuous.continuousAt (x := x)
  filter_upwards [hc.tendsto.eventually hp] with y hpy
  rwa [sourceMetric_pullback] at hpy

theorem source_actual_collar_coordinate_DEC {K : Set MatrixThreeJet} (hK : IsCompact K)
    (hreg : ∀ q ∈ K, Matrix.PosDef (fun i k => (q i k).1.1))
    {B : ℝ} (hB : 0 ≤ B) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ (R : ℝ) (f : SourceTensorFields) (ρ : ℝ) (x : AP),
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
      CKSAngularGeometry.coordinateDEC
        (CKSAngularGeometry.fieldNullInput
          (CKSAngularGeometry.oldParams (CKSBending.collarParams R (Real.exp ρ)))
          ((sourceCollarData f.logFields).angular ρ) x) (Real.exp ρ) →
      CKSAngularGeometry.coordinateDEC
        (CKSAngularGeometry.fieldNullInput (CKSBending.collarParams R (Real.exp ρ))
          ((sourceCollarData f.logFields).angular ρ) x) (Real.exp ρ) := by
  obtain ⟨R₀,hR₀,hh⟩ := cks_actual_collar_coordinate_DEC hK hreg hB
  refine ⟨R₀,hR₀,?_⟩
  intro R f ρ x hR hr htop hf hmk hek hp hσ hs hmg hmK hmr hb hold
  have hmk' := hmk
  rw [angularProjection_logRadiusChart] at hmk'
  have hcl := (logRadiusChart_smooth.contDiffAt (x := slice ρ x)).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)
  exact hh R f.logFields ρ x hR hr htop (source_tensor_log_regular hf)
    (angularLift_diff hmk') (hek.comp _ hcl) (source_tensor_log_positive hp) hσ
    (source_tensor_log_bounds hB hf hs hmg hmK hmr hb) hold

end
end CKSMixedGeometry

end

end OAI
