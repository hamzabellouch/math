import OAI.Geometry.EinsteinFour.WeylGeometry
import Mathlib.MeasureTheory.Measure.Hausdorff

namespace OAI

/-! The measure in the geometric application is fixed by the metric. In four
Euclidean dimensions the diameter-normalized Hausdorff measure is multiplied
by the unit-ball factor `(pi^2 / 2) / 2^4`. Positivity and finiteness are kept
separate from the elementary probability normalization. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Bundle
open scoped Manifold ContDiff ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]

/-- Canonically normalized four-dimensional Riemannian volume, constructed
from the actual length metric rather than an unspecified measure. -/
def volumeMeasure (g : SmoothMetric M) : Measure M := by
  letI : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle FourSpace (TangentSpace I4 : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I4 M
  exact ENNReal.ofReal (Real.pi ^ 2 / 32) • Measure.hausdorffMeasure 4

def totalVolume (g : SmoothMetric M) : ℝ := (volumeMeasure g Set.univ).toReal

/-- The volume ratio with the curvature-one round four-sphere. -/
def volumeRatio (g : SmoothMetric M) : ℝ := totalVolume g / (8 * Real.pi ^ 2 / 3)

def normalizedVolume (g : SmoothMetric M) : Measure M :=
  (volumeMeasure g Set.univ)⁻¹ • volumeMeasure g

/-- Compact Riemannian volume has positive finite mass. The normalization
argument below only needs these two facts, and does not assume a volume bound. -/
structure FinitePositiveVolume (g : SmoothMetric M) : Prop where
  positive : 0 < volumeMeasure g Set.univ
  finite : volumeMeasure g Set.univ < (∞ : ℝ≥0∞)

theorem normalizedVolume_isProbability {g : SmoothMetric M} (h : FinitePositiveVolume g) :
    IsProbabilityMeasure (normalizedVolume g) := by
  constructor
  change ((volumeMeasure g Set.univ)⁻¹ • volumeMeasure g) Set.univ = 1
  rw [Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (ne_of_gt h.positive) (ne_of_lt h.finite)

theorem totalVolume_pos {g : SmoothMetric M} (h : FinitePositiveVolume g) :
    0 < totalVolume g := by
  exact ENNReal.toReal_pos (ne_of_gt h.positive) (ne_of_lt h.finite)

theorem volumeRatio_pos {g : SmoothMetric M} (h : FinitePositiveVolume g) :
    0 < volumeRatio g := by
  exact div_pos (totalVolume_pos h) (by positivity)

end

end PositiveEinsteinFour.Geometry

end OAI
