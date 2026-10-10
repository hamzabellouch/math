import OAI.Geometry.RCD.Coordinates.UniformTransformation
import OAI.Geometry.RCD.Metric.ModelScaleControl

namespace OAI

/-! # The exact transformation input follows from measured Euclidean coordinates -/

open Set Metric
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.transformationInput_of_measured {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular]
    (hMeasured : LocalMeasuredCoordinateInput hX) : LocalTransformationInput hX := by
  intro hn β η hβ _
  obtain ⟨m,hm⟩ : ∃ m : ℕ, n=m+1 := ⟨n-1,(Nat.sub_add_cancel (by omega : 1≤n)).symm⟩
  subst n
  obtain ⟨a,ha,hBG,hscale⟩ := hX.model_comparison_with_scale_control hn
  have hBG' : BallVolumeComparison (hausdorff (m+1) X) (comparisonModelVolume m a) := by
    simpa only [Nat.add_sub_cancel] using hBG
  obtain ⟨δ,hδ,htransform⟩ := hX.uniform_transformation_of_measured m hn ha hBG' hMeasured β hβ
  refine ⟨min δ (1/9),lt_min hδ (by norm_num),?_⟩
  intro p R hR hK u v hfirst hflat t ht htR
  have hKδ : -δ ≤ K*R^2 := (neg_le_neg (min_le_left _ _)).trans hK
  have hKsmall : -(1/9 : ℝ) ≤ K*R^2 := (neg_le_neg (min_le_right _ _)).trans hK
  apply htransform p R hR hKδ (hscale R hR hKsmall) u v
    (hfirst.mono_error _ _ (le_of_lt (lt_min hδ (by norm_num))) (min_le_left _ _))
    _ t ht htR
  intro s hs hsR
  obtain ⟨f,hf⟩ := (hflat s hs hsR).1
  exact ⟨f,hf.mono_error (min_le_left _ _)⟩

end RegularPointCoordinates

end

end OAI
