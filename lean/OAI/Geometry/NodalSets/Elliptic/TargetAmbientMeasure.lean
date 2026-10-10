import OAI.Geometry.NodalSets.Elliptic.CompactDifferentialBound
import OAI.Geometry.NodalSets.Model

namespace OAI

namespace Yau.Target
open Bundle Manifold Set MeasureTheory
open scoped ENNReal NNReal ContDiff
noncomputable section
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F]

theorem smooth_projection_nodal_measure (g : SmoothMetric) (P : Manifold5 → F)
    (hP : ContMDiff modelWithCorners 𝓘(ℝ,F) ∞ P) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ (u : Manifold5 → ℝ) (Z : Set F),
      Z ⊆ P '' {x | u x = 0} →
      Measure.hausdorffMeasure (4:ℝ) Z ≤ (C : ℝ≥0∞)^4 * nodalMeasure g u := by
  let : RiemannianBundle (fun x : Manifold5 ↦ TangentSpace modelWithCorners x) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle Model
      (fun x : Manifold5 ↦ TangentSpace modelWithCorners x) :=
    ⟨g.inner, g.contMDiff.continuous, fun x v w ↦ rfl⟩
  obtain ⟨C,hpos,hC⟩ := Yau.Geometry.compact_map_edist_bound P (hP.of_le (by simp))
  let : MeasurableSpace Manifold5 := borel Manifold5
  let : BorelSpace Manifold5 := ⟨rfl⟩
  let : EMetricSpace Manifold5 := EMetricSpace.ofRiemannianMetric modelWithCorners Manifold5
  let : PseudoEMetricSpace Manifold5 :=
    (EMetricSpace.ofRiemannianMetric modelWithCorners Manifold5).toPseudoEMetricSpace
  have hLip : LipschitzWith C P := hC
  refine ⟨C,hpos,?_⟩
  intro u Z hZ
  have hh := (measure_mono hZ).trans
    (hLip.hausdorffMeasure_image_le (by norm_num : (0:ℝ) ≤ 4) {x | u x = 0})
  simpa only [show (4:ℝ) = (4:ℕ) by norm_num, ENNReal.rpow_natCast, nodalMeasure] using hh

end
end Yau.Target

end OAI
