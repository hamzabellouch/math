import OAI.Analysis.RCDHeat.Foundations
import Mathlib.MeasureTheory.Measure.Real

namespace OAI

/-!
# Transferring volume information between centers and scales

The comparison hypothesis is the cross-multiplied ball-volume inequality
from Bishop--Gromov. Its model function remains explicit, so the argument
applies to the negative-curvature models before taking the flat limit.
-/

open Metric MeasureTheory
open scoped ENNReal

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]

/-- The ball comparison in Sturm (2006), Theorem 2.3, equation (2.5),
written without divisions. For the application the model is the radial
volume of the constant negative-curvature comparison space. -/
def BallVolumeComparison (μ : Measure X) (model : ℝ → ℝ) : Prop :=
  ∀ y : X, ∀ r R : ℝ, 0 < r → r ≤ R →
    μ.real (ball y R) * model r ≤ μ.real (ball y r) * model R

/-- A central large ball lies in a slightly enlarged ball about every
nearby center, so its volume gives a lower bound at every smaller scale. -/
theorem volume_lower_at_nearby_center
    {μ : Measure X} {model : ℝ → ℝ} (hcomparison : BallVolumeComparison μ model)
    {p y : X} {R D r a : ℝ} (hy : dist p y ≤ D) (hr : 0 < r)
    (hrR : r ≤ R + D) (hmodelr : 0 ≤ model r) (hmodelR : 0 < model (R + D))
    (hfinite : μ (ball y (R + D)) ≠ ∞)
    (hlarge : a * model (R + D) ≤ μ.real (ball p R)) :
    a * model r ≤ μ.real (ball y r) := by
  have hsubset : ball p R ⊆ ball y (R + D) :=
    ball_subset_ball' (by linarith)
  have hvolume : μ.real (ball p R) ≤ μ.real (ball y (R + D)) :=
    measureReal_mono hsubset hfinite
  have hcross : a * model r * model (R + D) ≤
      μ.real (ball y r) * model (R + D) := by
    calc
      _ = (a * model (R + D)) * model r := by ring
      _ ≤ μ.real (ball y (R + D)) * model r :=
        mul_le_mul_of_nonneg_right (hlarge.trans hvolume) hmodelr
      _ ≤ _ := hcomparison y r (R + D) hr hrR
  exact (mul_le_mul_iff_left₀ hmodelR).mp hcross

/-- Uniform large-scale information is inherited by every center and
every positive smaller radius, without a lower cutoff on that radius. -/
theorem uniform_volume_lower_on_ball
    {μ : Measure X} {model : ℝ → ℝ} (hcomparison : BallVolumeComparison μ model)
    {p : X} {R D a : ℝ} (hmodel : ∀ r, 0 < r → 0 < model r)
    (hRD : 0 < R + D)
    (hfinite : ∀ y, μ (ball y (R + D)) ≠ ∞)
    (hlarge : a * model (R + D) ≤ μ.real (ball p R)) :
    ∀ y, dist p y ≤ D → ∀ r, 0 < r → r ≤ R + D →
      a * model r ≤ μ.real (ball y r) := by
  intro y hy r hr hrR
  exact volume_lower_at_nearby_center hcomparison hy hr hrR
    (hmodel r hr).le (hmodel _ hRD) (hfinite y) hlarge

/-- A weak form of an upper density bound: arbitrarily small radii
approach the given upper bound. Bishop--Gromov propagates it to all radii. -/
def SmallScaleVolumeUpper (μ : Measure X) (model : ℝ → ℝ) (y : X) (a : ℝ) : Prop :=
  ∀ delta : ℝ, 0 < delta → ∀ R : ℝ, 0 < R →
    ∃ r : ℝ, 0 < r ∧ r < R ∧ μ.real (ball y r) ≤ (a + delta) * model r

theorem volume_upper_of_small_scale_upper
    {μ : Measure X} {model : ℝ → ℝ} (hcomparison : BallVolumeComparison μ model)
    (hmodel : ∀ r, 0 < r → 0 < model r) {y : X} {a R : ℝ}
    (hdensity : SmallScaleVolumeUpper μ model y a) (hR : 0 < R) :
    μ.real (ball y R) ≤ a * model R := by
  have hquotient : μ.real (ball y R) / model R ≤ a := by
    apply le_of_forall_pos_le_add
    intro delta hdelta
    obtain ⟨r, hr, hrR, hv⟩ := hdensity delta hdelta R hR
    have hstep := hcomparison y r R hr hrR.le
    have hcross : μ.real (ball y R) * model r ≤
        ((a + delta) * model R) * model r := by
      calc
        _ ≤ μ.real (ball y r) * model R := hstep
        _ ≤ ((a + delta) * model r) * model R :=
          mul_le_mul_of_nonneg_right hv (hmodel R hR).le
        _ = _ := by ring
    exact (div_le_iff₀ (hmodel R hR)).mpr
      ((mul_le_mul_iff_left₀ (hmodel r hr)).mp hcross)
  exact (div_le_iff₀ (hmodel R hR)).mp hquotient

end RegularPointCoordinates

end OAI
