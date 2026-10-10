import Mathlib
import OAI.Analysis.BiholderTransport.Model

namespace OAI

section
section
noncomputable section
open Set Filter Manifold MeasureTheory Bundle Metric
open scoped Topology ContDiff ENNReal NNReal

namespace WeakMTWTransport
section ForwardChart
variable {n : ℕ} {M : Type*} [MetricSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace
end ForwardChart
end WeakMTWTransport

end

end

section

noncomputable section
open Set Filter Manifold MeasureTheory Bundle Metric
open scoped Topology ContDiff ENNReal NNReal

namespace WeakMTWTransport

lemma metricVolume_model (n : ℕ) : metricVolume (M := Model n) n=volume := by
  let μ : Measure (Model n) := Measure.hausdorffMeasure (n:ℝ)
  have hdim : Module.finrank ℝ (Model n)=n := by simp [Model]
  have : μ.IsAddHaarMeasure := by
    dsimp only [μ]
    rw [←hdim]
    infer_instance
  change _ • μ=volume
  exact (measure_eq_sub_vadd volume μ
    (measure_ball_pos μ (0:Model n) zero_lt_one).ne' measure_ball_lt_top.ne).symm

lemma metricVolume_lipschitz_image_le {n : ℕ} {X Y : Type*}
    [MetricSpace X] [MetricSpace Y] [MeasurableSpace X] [MeasurableSpace Y]
    [BorelSpace X] [BorelSpace Y] {f : X → Y} {s : Set X} {C : ℝ≥0}
    (hf : LipschitzOnWith C f s) :
    metricVolume n (f '' s)≤(C:ℝ≥0∞)^(n:ℝ)*metricVolume n s := by
  have H := hf.hausdorffMeasure_image_le (d := (n:ℝ)) (by positivity)
  change euclideanVolumeFactor n*(Measure.hausdorffMeasure (n:ℝ) (f '' s))≤
    (C:ℝ≥0∞)^(n:ℝ)*(euclideanVolumeFactor n*(Measure.hausdorffMeasure (n:ℝ) s))
  calc
    _ ≤ euclideanVolumeFactor n*((C:ℝ≥0∞)^(n:ℝ)*(Measure.hausdorffMeasure (n:ℝ) s)) := mul_le_mul_right H _
    _ = _ := by ac_rfl

end WeakMTWTransport
end
end
end

end OAI
