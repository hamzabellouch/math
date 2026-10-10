import OAI.Geometry.RCD.Metric.RecenterApproximation
import OAI.Geometry.RCD.Coordinates.SplittingApproximation

namespace OAI

/-!
# The published half-ball volume-rigidity input

De Philippis--Gigli (2018), Theorem 1.6, gives GH control of the half ball.
We retain that radius loss and use an unpointed ball approximation. The
centering and fixed metric-rescaling steps are proved in Lean.
-/

open Metric MeasureTheory

noncomputable section

namespace RegularPointCoordinates

def euclideanUnitVolume (n : ℕ) : ℝ :=
  volume.real (ball (0 : Euclidean n) 1)

theorem euclideanUnitVolume_pos (n : ℕ) : 0 < euclideanUnitVolume n := by
  exact ENNReal.toReal_pos (ne_of_gt (measure_ball_pos volume (0 : Euclidean n) (by norm_num)))
    (ne_of_lt measure_ball_lt_top)

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The map formulation of De Philippis--Gigli Theorem 1.6. The universal
error absorbs the usual factor between GH distance and approximation maps. -/
def LocalVolumeRigidityInput {K : ℝ} {n : ℕ} (_hX : NoncollapsedRCD K n X) : Prop :=
  2 ≤ n → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ (p : X) (R : ℝ), 0 < R → -δ ≤ K * R ^ 2 →
      (1 - δ) * euclideanUnitVolume n * R ^ n < (hausdorff n X).real (ball p R) →
      ∃ f : X → Euclidean n, IsBallApproximation p 0 R (1 / 2) ε f

/-- Nearly maximal volume on B_(4r) yields a pointed Euclidean
approximation on B_(2r), with the prescribed normalized error. -/
theorem pointed_flatness_of_volume_rigidity {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) (hpublished : LocalVolumeRigidityInput hX)
    {θ : ℝ} (hθ : 0 < θ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (p : X) (r : ℝ), 0 < r → -δ ≤ K * (4 * r) ^ 2 →
      (1 - δ) * euclideanUnitVolume n * (4 * r) ^ n ≤
        (hausdorff n X).real (ball p (4 * r)) →
      ∃ f : X → Euclidean n, IsPointedApproximation p 0 r 2 θ f := by
  let ε := min (1 / 4 : ℝ) (θ / 16)
  have hε : 0 < ε := lt_min (by norm_num) (by positivity)
  obtain ⟨d, hd, happly⟩ := hpublished hn ε hε
  refine ⟨d / 2, by positivity, ?_⟩
  intro p r hr hcurv hvol
  have hstrict : (1 - d) * euclideanUnitVolume n * (4 * r) ^ n <
      (hausdorff n X).real (ball p (4 * r)) := by
    have hmul : 0 < euclideanUnitVolume n * (4 * r) ^ n :=
      mul_pos (euclideanUnitVolume_pos n) (pow_pos (by positivity) n)
    nlinarith
  obtain ⟨f, hf⟩ := happly p (4 * r) (by positivity) (by linarith) hstrict
  have hεhalf : ε < 1 / 2 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hp := (hf.recenter (by positivity) hε.le hεhalf).rescale_four hr
  refine ⟨fun x => (4 : ℝ) • (f x - f p), hp.mono_error ?_⟩
  have hh : ε ≤ θ / 16 := min_le_right _ _
  linarith

end RegularPointCoordinates

end

end OAI
