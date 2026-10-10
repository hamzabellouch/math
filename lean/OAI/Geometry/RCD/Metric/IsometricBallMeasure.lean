import OAI.Geometry.RCD.Coordinates.RegularMetricLimitMeasure
import Mathlib.MeasureTheory.Measure.Restrict

namespace OAI

/-! # Transporting a local metric measure through a closed-ball isometry -/

open Set Metric MeasureTheory Filter
noncomputable section
namespace RegularPointCoordinates
variable {Y E : Type*} [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  [MetricSpace E] [MeasurableSpace E] [BorelSpace E]

def isometricBallMeasure (μ : Measure Y) (q : Y) (R : ℝ)
    (f : closedBall q R → E) : Measure E :=
  (μ.comap (Subtype.val : closedBall q R → Y)).map f

omit [MetricSpace E] [BorelSpace E] in
theorem isometricBallMeasure_finite (μ : Measure Y) [IsFiniteMeasure μ]
    (q : Y) (R : ℝ) (f : closedBall q R → E) :
    IsFiniteMeasure (isometricBallMeasure μ q R f) := by
  have he := MeasurableEmbedding.subtype_coe (measurableSet_closedBall (x := q) (ε := R))
  let : IsFiniteMeasure (μ.comap (Subtype.val : closedBall q R → Y)) := ⟨by
    rw [he.comap_apply]
    exact measure_lt_top _ _⟩
  unfold isometricBallMeasure
  infer_instance

theorem isometricBallMeasure_supported [ProperSpace Y] (μ : Measure Y) (q : Y) (R : ℝ)
    (f : closedBall q R → E) (hf : Isometry f) :
    ∀ᵐ x ∂isometricBallMeasure μ q R f, x ∈ range f := by
  unfold isometricBallMeasure
  have hK : IsCompact (range f) := by
    simpa only [image_univ] using isCompact_univ.image hf.continuous
  apply (ae_map_iff hf.continuous.measurable.aemeasurable
    hK.measurableSet).mpr
  exact Eventually.of_forall (fun x => mem_range_self x)

theorem isometricBallMeasure_closedBall (μ : Measure Y) {q : Y} {R : ℝ}
    (f : closedBall q R → E) (hf : Isometry f)
    (x : closedBall q R) (t : ℝ) (ht : dist (x:Y) q+t ≤ R) :
    isometricBallMeasure μ q R f (closedBall (f x) t) = μ (closedBall (x:Y) t) := by
  have he := MeasurableEmbedding.subtype_coe (measurableSet_closedBall (x := q) (ε := R))
  rw [isometricBallMeasure,Measure.map_apply hf.continuous.measurable measurableSet_closedBall,
    he.comap_apply]
  congr 1
  ext y
  constructor
  · rintro ⟨z,hz,rfl⟩
    change dist (f z) (f x) ≤ t at hz
    simpa only [hf.dist_eq,Subtype.dist_eq,mem_closedBall] using hz
  · intro hy
    have hyR : y ∈ closedBall q R := by
      change dist y q ≤ R
      have htri := dist_triangle y (x:Y) q
      change dist y (x:Y) ≤ t at hy
      linarith
    refine ⟨⟨y,hyR⟩,?_,rfl⟩
    change dist (f ⟨y,hyR⟩) (f x) ≤ t
    simpa only [hf.dist_eq,Subtype.dist_eq,mem_closedBall] using hy

theorem isometricBallMeasure_ball (μ : Measure Y) {q : Y} {R : ℝ}
    (f : closedBall q R → E) (hf : Isometry f)
    (x : closedBall q R) (t : ℝ) (ht : dist (x:Y) q+t ≤ R) :
    isometricBallMeasure μ q R f (ball (f x) t) = μ (ball (x:Y) t) := by
  have he := MeasurableEmbedding.subtype_coe (measurableSet_closedBall (x := q) (ε := R))
  rw [isometricBallMeasure,Measure.map_apply hf.continuous.measurable measurableSet_ball,
    he.comap_apply]
  congr 1
  ext y
  constructor
  · rintro ⟨z,hz,rfl⟩
    change dist (f z) (f x) < t at hz
    simpa only [hf.dist_eq,Subtype.dist_eq,mem_ball] using hz
  · intro hy
    have hyR : y ∈ closedBall q R := by
      change dist y q ≤ R
      have htri := dist_triangle y (x:Y) q
      change dist y (x:Y) < t at hy
      linarith
    refine ⟨⟨y,hyR⟩,?_,rfl⟩
    change dist (f ⟨y,hyR⟩) (f x) < t
    simpa only [hf.dist_eq,Subtype.dist_eq,mem_ball] using hy

end RegularPointCoordinates

end

end OAI
