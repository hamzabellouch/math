import OAI.Geometry.Relativity.CKS.SourcePhysicalFoliation
import OAI.Geometry.Relativity.CKS.SourceFoliationLeading
import OAI.Geometry.Relativity.CKS.CKSFoliationAsymptotics
import OAI.Geometry.Relativity.CKS.ScaledJetOutput

namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter Matrix
open CKSAngularGeometry (determinant determinant_eq)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

theorem cks_source_foliation_asymptotics {K : Set MatrixThreeJet} (hK : IsCompact K)
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
      ScaledComponentBound (fun y => sourceExpansion f y-1-sourceLeadingD f y/(y 0)^3) 2 4 C (logRadiusChart x) ∧
      ScaledComponentBound (fun y => sourceT f y-1-sourceLeadingT f y/(y 0)^3) 2 4 C (logRadiusChart x) ∧
      ScaledComponentBound (fun y => sourceLapse f y/Real.sqrt (1+(y 0)^2)-1-sourceLeadingLapse f y/(y 0)^3) 2 4 C (logRadiusChart x) ∧
      ScaledComponentBound (fun y => sourceU f y/Real.sqrt (1+(y 0)^2)-1-sourceLeadingU f y/(y 0)^3) 2 4 C (logRadiusChart x) := by
  obtain ⟨R,hR,C,hC,hh⟩ := cks_physical_foliation_asymptotics hK hreg hB
  refine ⟨R,hR,C,hC,?_⟩
  intro f x hr hf hp hσ hs hmg hmk hmr hb
  have hn := source_logFields_regular hf
  obtain ⟨heg,hek,hb',herr⟩ := source_log_remainder_bounds hB hf hb
  have hpLog : ∀ᶠ y in 𝓝 x, (logMetric f.logFields y).PosDef := by
    have hc := logRadiusChart_smooth.continuous.continuousAt (x := x)
    filter_upwards [hc.tendsto.eventually hp] with y hpy
    rwa [sourceMetric_pullback] at hpy
  obtain ⟨hD,hT,hL,hU⟩ := hh f.logFields x hr hn hpLog hσ hs hmg heg hmk hek hb' hmr herr
  have hy : (logRadiusChart x) 0 ≠ 0 := by simp [logRadiusChart]
  have hpos := hp.self_of_nhds
  have h0 : determinant (sourceGamma f (logRadiusChart x)) ≠ 0 := by
    rw [determinant_eq]
    exact (CKSAngularGeometry.metricBlock_leaf_posDef hpos).det_pos.ne'
  have hσ0 : determinant (f.sigma (angularProjection (logRadiusChart x))) ≠ 0 := by
    rw [angularProjection_logRadiusChart]
    exact hreg _ hσ
  have hrad : ContDiffAt ℝ 2 (fun y : Point => y 0) (logRadiusChart x) := by fun_prop
  have hsqrt : ContDiffAt ℝ 2 (fun y : Point => Real.sqrt (1+(y 0)^2)) (logRadiusChart x) :=
    (contDiffAt_const.add (hrad.pow 2)).sqrt (by positivity)
  have hsqrt0 : Real.sqrt (1+((logRadiusChart x) 0)^2) ≠ 0 := by positivity
  have hnear : ∀ᶠ y in 𝓝 x, f.RegularAt (logRadiusChart y) ∧
      determinant (sourceGamma f (logRadiusChart y)) ≠ 0 := by
    have hc := logRadiusChart_smooth.continuous.continuousAt (x := x)
    filter_upwards [hc.tendsto.eventually hf.eventually,hc.tendsto.eventually hp] with y hfy hpy
    exact ⟨hfy,by rw [determinant_eq]; exact (CKSAngularGeometry.metricBlock_leaf_posDef hpy).det_pos.ne'⟩
  refine ⟨?_,?_,?_,?_⟩
  · apply source_scaled_bound_of_jet (((sourceExpansion_regular hf hy h0).sub contDiffAt_const).sub ((sourceLeadingD_regular hf hσ0).fun_div (hrad.pow 3) (pow_ne_zero _ hy)))
    have heq : actualScalarJet (fun y => sourceExpansion f (logRadiusChart y)-1-sourceLeadingD f (logRadiusChart y)/((logRadiusChart y) 0)^3) x =
        actualScalarJet (fun y => logExpansion f.logFields y-1-radiusPower (-3) y*leadingDField f.logFields y) x := by
      apply actualScalarJet_congr
      filter_upwards [hnear] with y hy
      rw [sourceExpansion_pullback hy.1 hy.2,sourceLeadingD_pullback,radiusPower_minus_three]
      simp only [logRadiusChart,ite_true]
      ring
    rwa [heq]
  · apply source_scaled_bound_of_jet (((sourceT_regular hf hy hpos).sub contDiffAt_const).sub ((sourceLeadingT_regular hf hσ0).fun_div (hrad.pow 3) (pow_ne_zero _ hy)))
    have heq : (fun y => sourceT f (logRadiusChart y)-1-sourceLeadingT f (logRadiusChart y)/((logRadiusChart y) 0)^3) = fun y => logT f.logFields y-1-radiusPower (-3) y*leadingTField f.logFields y := by
      funext y
      rw [congrFun (sourceT_pullback f) y,sourceLeadingT_pullback,radiusPower_minus_three]
      simp only [logRadiusChart,ite_true]
      ring
    simpa only [heq] using hT
  · apply source_scaled_bound_of_jet ((((sourceLapse_regular hf hy hpos).fun_div hsqrt hsqrt0).sub contDiffAt_const).sub ((sourceLeadingLapse_regular hf).fun_div (hrad.pow 3) (pow_ne_zero _ hy)))
    have heq : (fun y => sourceLapse f (logRadiusChart y)/Real.sqrt (1+((logRadiusChart y) 0)^2)-1-sourceLeadingLapse f (logRadiusChart y)/((logRadiusChart y) 0)^3) =
        fun y => logLapse f.logFields y/Real.sqrt (1+Real.exp (y 0)^2)-1-radiusPower (-3) y*leadingLapseField f.logFields y := by
      funext y
      rw [congrFun (sourceLapse_pullback f) y,sourceLeadingLapse_pullback,radiusPower_minus_three]
      simp only [logRadiusChart,ite_true]
      ring
    simpa only [heq] using hL
  · apply source_scaled_bound_of_jet ((((sourceU_regular hf hy hpos).fun_div hsqrt hsqrt0).sub contDiffAt_const).sub ((sourceLeadingU_regular hf hσ0).fun_div (hrad.pow 3) (pow_ne_zero _ hy)))
    have heq : actualScalarJet (fun y => sourceU f (logRadiusChart y)/Real.sqrt (1+((logRadiusChart y) 0)^2)-1-sourceLeadingU f (logRadiusChart y)/((logRadiusChart y) 0)^3) x =
        actualScalarJet (fun y => logU f.logFields y/Real.sqrt (1+Real.exp (y 0)^2)-1-radiusPower (-3) y*leadingUField f.logFields y) x := by
      apply actualScalarJet_congr
      filter_upwards [hnear] with y hy
      rw [sourceU_pullback hy.1 hy.2,sourceLeadingU_pullback,radiusPower_minus_three]
      simp only [logRadiusChart,ite_true]
      ring
    rwa [heq]

end
end CKSMixedGeometry

end

end OAI
