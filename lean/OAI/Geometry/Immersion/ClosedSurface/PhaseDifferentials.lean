import OAI.Geometry.Immersion.ClosedSurface.AtlasPhases

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4
open SmallModes RealModes PhaseGeometry Set Filter
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

lemma phaseDerivative_add {f g : SmallModes.Base → ℝ} {x : SmallModes.Base}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    phaseDerivative (f+g) x = phaseDerivative f x + phaseDerivative g x := by
  unfold phaseDerivative
  rw [fderiv_add hf hg]
  rfl

lemma phaseDerivative_sub {f g : SmallModes.Base → ℝ} {x : SmallModes.Base}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    phaseDerivative (f-g) x = phaseDerivative f x - phaseDerivative g x := by
  unfold phaseDerivative
  rw [fderiv_sub hf hg]
  rfl

lemma phaseDerivative_const_smul {f : SmallModes.Base → ℝ} {x : SmallModes.Base}
    (hf : DifferentiableAt ℝ f x) (c : ℝ) :
    phaseDerivative (c • f) x = c • phaseDerivative f x := by
  unfold phaseDerivative
  rw [fderiv_const_smul hf]
  rfl

lemma atlasPhase_in_chart_differentiable (q p : M) (ξ : SmallModes.Base)
    {a : M} (hap : a ∈ (coordinateChart p).source) (haq : a ∈ (coordinateChart q).source) :
    DifferentiableAt ℝ (atlasPhase q ξ ∘ (coordinateChart p).symm) (coordinateChart p a) := by
  have hx := coordinateTransition_mem_chart q p hap haq
  have ht := ((coordinateTransition_smoothOn q p) _ hx).contDiffAt
    ((coordinateTransition q p).open_source.mem_nhds hx)
  exact (phaseLinear ξ).differentiableAt.comp _ (ht.differentiableAt (by simp))



theorem atlasPhaseCovector_add (q r p : M) (ξ υ : SmallModes.Base) (c d : ℝ)
    {a : M} (hap : a ∈ (coordinateChart p).source)
    (haq : a ∈ (coordinateChart q).source) (har : a ∈ (coordinateChart r).source) :
    phaseDerivative (((c • atlasPhase q ξ) + (d • atlasPhase r υ)) ∘ (coordinateChart p).symm)
      (coordinateChart p a) =
      c • atlasPhaseCovector q p ξ a + d • atlasPhaseCovector r p υ a := by
  have hq := atlasPhase_in_chart_differentiable q p ξ hap haq
  have hr := atlasPhase_in_chart_differentiable r p υ hap har
  change phaseDerivative ((c • (atlasPhase q ξ ∘ (coordinateChart p).symm)) +
    (d • (atlasPhase r υ ∘ (coordinateChart p).symm))) (coordinateChart p a) = _
  rw [phaseDerivative_add (hq.const_smul c) (hr.const_smul d),
    phaseDerivative_const_smul hq c,phaseDerivative_const_smul hr d]
  rfl

theorem atlasPhaseCovector_sub (q r p : M) (ξ υ : SmallModes.Base) (c d : ℝ)
    {a : M} (hap : a ∈ (coordinateChart p).source)
    (haq : a ∈ (coordinateChart q).source) (har : a ∈ (coordinateChart r).source) :
    phaseDerivative (((c • atlasPhase q ξ) - (d • atlasPhase r υ)) ∘ (coordinateChart p).symm)
      (coordinateChart p a) =
      c • atlasPhaseCovector q p ξ a - d • atlasPhaseCovector r p υ a := by
  have hq := atlasPhase_in_chart_differentiable q p ξ hap haq
  have hr := atlasPhase_in_chart_differentiable r p υ hap har
  change phaseDerivative ((c • (atlasPhase q ξ ∘ (coordinateChart p).symm)) -
    (d • (atlasPhase r υ ∘ (coordinateChart p).symm))) (coordinateChart p a) = _
  rw [phaseDerivative_sub (hq.const_smul c) (hr.const_smul d),
    phaseDerivative_const_smul hq c,phaseDerivative_const_smul hr d]
  rfl

end ClosedSurfaceR4

end

end OAI
