import OAI.Geometry.Relativity.CKS.SourcePhysicalMass

namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter Matrix
open CKSAngularGeometry (determinant inverse)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def sourceAspect (f : SourceMassFields) (w : Angle) : ℝ :=
  traceProduct (inverse (f.sigma w)) (f.mg w+(2:ℝ) • f.mK w)+2*f.mr w

lemma source_leading_mass (f : SourceMassFields) : cksLeadingField f.logFields =
    fun y => sourceAspect f (angularProjection y)/4 := by
  funext y
  unfold cksLeadingField SourceMassFields.logFields angularLift sourceAspect
  rw [traceProduct_add,traceProduct_smul]
  ring

lemma SourceMassFields.RegularAt.eventually {f : SourceMassFields} {x : Point} (hf : f.RegularAt x) :
    ∀ᶠ y in 𝓝 x, f.RegularAt y := by
  have hc := angularProjection.continuous.continuousAt (x := x)
  filter_upwards [hc.tendsto.eventually (hf.sigma.eventually (by norm_num)),
    hc.tendsto.eventually (hf.mg.eventually (by norm_num)),
    hc.tendsto.eventually (hf.mK.eventually (by norm_num)),
    hc.tendsto.eventually (hf.mr.eventually (by norm_num)),
    hf.eg.eventually (by norm_num),hf.ek.eventually (by norm_num),
    hf.b.eventually (by norm_num),hf.err.eventually (by norm_num)]
    with y hs hm hk hmr he hek hb herr
  exact ⟨hs,hm,hk,hmr,he,hek,hb,herr⟩

lemma sourcePhysicalMass_jet_pullback {f : SourceMassFields} {x : Point}
    (hf : f.RegularAt (logRadiusChart x))
    (hp : ∀ᶠ y in 𝓝 (logRadiusChart x), (sourceMetric f y).PosDef) :
    actualScalarJet (fun y => sourcePhysicalMass f (logRadiusChart y)) x =
      actualScalarJet (logPhysicalMass f.logFields) x := by
  apply actualScalarJet_congr
  have hc := logRadiusChart_smooth.continuous.continuousAt (x := x)
  filter_upwards [hc.tendsto.eventually hf.eventually,hc.tendsto.eventually hp] with y hy hpy
  exact sourcePhysicalMass_pullback hy hpy

theorem cks_source_mass_mixed {K : Set MatrixThreeJet} (hK : IsCompact K)
    (hreg : ∀ q ∈ K, determinant (fun i k => (q i k).1.1) ≠ 0)
    {B : ℝ} (hB : 0 ≤ B) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ f : SourceMassFields, ∀ x : Point,
      R₀ ≤ Real.exp (x 0) → f.RegularAt (logRadiusChart x) →
      (∀ᶠ y in 𝓝 (logRadiusChart x), (sourceMetric f y).PosDef) →
      matrixThreeJets (angularLift f.sigma) x ∈ K →
      ‖matrixThreeJets (angularLift f.sigma) x‖ ≤ B →
      ‖matrixThreeJets (angularLift f.mg) x‖ ≤ B →
      ‖matrixScalarJets (angularLift f.mK) x‖ ≤ B →
      ‖actualScalarJet (angularLift f.mr) x‖ ≤ B →
      f.ComponentBounds B (logRadiusChart x) →
      ‖actualScalarJet (fun y => sourcePhysicalMass f (logRadiusChart y)) x-
        actualScalarJet (fun y => sourceAspect f (angularProjection y)/4) x‖ ≤
        C/Real.exp (x 0) := by
  obtain ⟨R,hR,C,hC,hh⟩ := cks_physical_mass_mixed hK hreg hB
  refine ⟨R,hR,C,hC,?_⟩
  intro f x hr hf hp hσ hs hmg hmk hmr hb
  have hn := source_logFields_regular hf
  obtain ⟨heg,hek,hb',herr⟩ := source_log_remainder_bounds hB hf hb
  have hpLog : ∀ᶠ y in 𝓝 x, (logMetric f.logFields y).PosDef := by
    have hc := logRadiusChart_smooth.continuous.continuousAt (x := x)
    filter_upwards [hc.tendsto.eventually hp] with y hpy
    rwa [sourceMetric_pullback] at hpy
  rw [sourcePhysicalMass_jet_pullback hf hp,← source_leading_mass]
  exact hh f.logFields x hr hn hpLog hσ hs hmg heg hmk hek hb' hmr herr

end
end CKSMixedGeometry

end

end OAI
