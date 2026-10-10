import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.MetricDefinitions
import OAI.Analysis.BiholderTransport.Calculus.SecondTaylorComposition
import OAI.Analysis.BiholderTransport.Coordinates.ChartLipschitz

namespace OAI

section
section
noncomputable section
open Set Filter Manifold MeasureTheory Bundle Metric
open scoped Topology ContDiff ENNReal NNReal

namespace WeakMTWTransport
section AERademacher
variable {n : ℕ} {M : Type*} [MetricSpace M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma lipschitz_ae_mdifferentiableAt {f : M → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) :
    ∀ᵐ x ∂metricVolume (M := M) n, MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) f x := by
  have hlocal : ∀ x∈(univ : Set M), ∃ U : Set M, IsOpen U ∧ x∈U ∧
      (∀ᵐ z ∂metricVolume (M := M) n, z∈U → MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) f z) := by
    intro x _
    obtain ⟨C,r,hr,htarget,hLip⟩ := exists_lipschitz_inverse_chart (n := n) x
    let d := extChartAt 𝓘(ℝ,Model n) x
    let B := ball (d x) r
    let U := d.source ∩ d ⁻¹' B
    have hU : IsOpen U := (continuousOn_extChartAt x).isOpen_inter_preimage
      (isOpen_extChartAt_source x) isOpen_ball
    refine ⟨U,hU,⟨mem_extChartAt_source x,mem_ball_self hr⟩,?_⟩
    let μ : Measure (Model n) := Measure.hausdorffMeasure (n:ℝ)
    have hdim : Module.finrank ℝ (Model n)=n := by simp [Model]
    have : μ.IsAddHaarMeasure := by
      dsimp only [μ]
      rw [←hdim]
      infer_instance
    have hR := (hf.comp_lipschitzOnWith hLip).ae_differentiableWithinAt_of_mem (μ := μ)
    let N := {q : Model n | q∈B ∧ ¬DifferentiableAt ℝ (f ∘ d.symm) q}
    have hN : μ N=0 := by
      apply measure_mono_null _ (ae_iff.mp hR)
      intro q hq
      change ¬(q∈B → DifferentiableWithinAt ℝ (f ∘ d.symm) B q)
      intro hh
      exact hq.2 ((hh hq.1).differentiableAt (isOpen_ball.mem_nhds hq.1))
    have hNsub : N⊆B := fun _ h => h.1
    have hImage : (Measure.hausdorffMeasure (n:ℝ) : Measure M) (d.symm '' N)=0 := by
      apply le_antisymm _ (show (0:ℝ≥0∞)≤_ from zero_le)
      have H := (hLip.mono hNsub).hausdorffMeasure_image_le (d := (n:ℝ)) (by positivity)
      change _ ≤ (C : ℝ≥0∞)^(n:ℝ)*μ N at H
      simpa only [d,hN,mul_zero] using H
    have hImageVol : metricVolume (M := M) n (d.symm '' N)=0 := by
      simp only [metricVolume,Measure.smul_apply,smul_eq_mul,hImage,mul_zero]
    apply ae_iff.mpr
    apply measure_mono_null _ hImageVol
    intro z hz
    have hz' : z∈U ∧ ¬MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) f z := by
      simpa only [mem_ofPred_eq,Classical.not_imp] using hz
    refine ⟨d z,⟨hz'.1.2,?_⟩,d.left_inv hz'.1.1⟩
    intro hD
    have hChart := mdifferentiableAt_extChartAt (I := 𝓘(ℝ,Model n))
      (show z∈(chartAt (Model n) x).source by simpa only [d,extChartAt_source] using hz'.1.1)
    have H := hD.hasFDerivAt.hasMFDerivAt.comp z hChart.hasMFDerivAt
    apply hz'.2
    apply (H.congr_of_eventuallyEq _).mdifferentiableAt
    filter_upwards [(isOpen_extChartAt_source x).mem_nhds hz'.1.1] with w hw
    change f w=f (d.symm (d w))
    rw [d.left_inv hw]
  simpa only [mem_univ,true_implies] using ae_of_locally_ae (metricVolume (M := M) n) hlocal

variable [CompactSpace M] [Nonempty M]
lemma cTransform_ae_mdifferentiableAt {v : M → ℝ} (hv : Continuous v) :
    ∀ᵐ x ∂metricVolume (M := M) n,
      MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (cTransform v) x := by
  exact lipschitz_ae_mdifferentiableAt (cTransform_lipschitz hv
    (D := ⟨Metric.diam (univ : Set M),Metric.diam_nonneg⟩) (fun x y =>
      Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ x) (mem_univ y)))

end AERademacher
end WeakMTWTransport

end

end

end

end OAI
