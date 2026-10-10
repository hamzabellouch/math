import OAI.Geometry.RCD.Metric.EuclideanBallDensity
import OAI.Geometry.RCD.Metric.DensityLawSupport
import OAI.Geometry.RCD.Metric.TranslatedDensityLaw

namespace OAI

/-! # Compact ball densities and their translated probability laws -/

open Set Filter MeasureTheory Metric
open scoped Topology BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates

theorem euclideanBallDensity_nonneg {n : ℕ} (x : Euclidean n) {a b : ℝ}
    (hab : a<b) (y : Euclidean n) : 0≤euclideanBallDensity x a b hab y :=
  (nestedBallCutoff_bounds x a b y).1

theorem euclideanBallDensity_zero {n : ℕ} (x : Euclidean n) {a b : ℝ}
    (hab : a<b) {y : Euclidean n} (hy : b≤dist y x) :
    euclideanBallDensity x a b hab y=0 :=
  nestedBallCutoff_eq_zero x hab (by simpa only [dist_comm] using hy)

theorem euclideanBallDensity_mass_pos {n : ℕ} (x : Euclidean n) {a b : ℝ}
    (ha : 0<a) (hab : a<b) : 0<∫ y, euclideanBallDensity x a b hab y :=
  (ENNReal.toReal_pos (measure_ball_pos volume x ha).ne' measure_ball_ne_top).trans_le
    (euclideanBallDensity_mass_lower x hab)

def euclideanBallDensityLaw {n : ℕ} (x : Euclidean n) {a b : ℝ}
    (ha : 0<a) (hab : a<b) : ProbabilityMeasure (Euclidean n) :=
  normalizedDensityLaw volume (euclideanBallDensity_integrable x hab)
    (euclideanBallDensity_nonneg x hab) (euclideanBallDensity_mass_pos x ha hab)

theorem euclideanBallDensityLaw_support {n : ℕ} (x : Euclidean n) {a b : ℝ}
    (ha : 0<a) (hab : a<b) :
    ∀ᵐ y ∂(euclideanBallDensityLaw x ha hab : Measure (Euclidean n)), dist y x≤b := by
  have hn := normalizedDensityLaw_ae_ne_zero volume
    (euclideanBallDensity x a b hab).continuous.measurable
    (euclideanBallDensity_integrable x hab) (euclideanBallDensity_nonneg x hab)
    (euclideanBallDensity_mass_pos x ha hab)
  exact hn.mono fun y hy => le_of_lt (lt_of_not_ge fun hz => hy
    (euclideanBallDensity_zero x hab hz))

theorem euclideanBallDensity_translate {n : ℕ} (x h y : Euclidean n) {a b : ℝ}
    (hab : a<b) :
    euclideanBallDensity (x+h) a b hab y=euclideanBallDensity x a b hab (y-h) := by
  change nestedBallCutoff (x+h) a b y=nestedBallCutoff x a b (y-h)
  simp only [nestedBallCutoff,dist_eq_norm]
  congr 3
  abel_nf

theorem euclideanBallDensityLaw_translate {n : ℕ} (x h : Euclidean n) {a b : ℝ}
    (ha : 0<a) (hab : a<b) :
    euclideanBallDensityLaw (x+h) ha hab=(euclideanBallDensityLaw x ha hab).map (fun y => y+h) :=
  normalized_density_translation (euclideanBallDensity x a b hab).continuous.measurable
    (euclideanBallDensity (x+h) a b hab).continuous.measurable
    (euclideanBallDensity_integrable x hab) (euclideanBallDensity_integrable (x+h) hab)
    (euclideanBallDensity_nonneg x hab) (euclideanBallDensity_nonneg (x+h) hab)
    (euclideanBallDensity_mass_pos x ha hab) (euclideanBallDensity_mass_pos (x+h) ha hab)
    h (euclideanBallDensity_translate x h · hab)

end RegularPointCoordinates

end

end OAI
