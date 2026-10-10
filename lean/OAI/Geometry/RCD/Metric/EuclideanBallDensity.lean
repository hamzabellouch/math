import OAI.Geometry.RCD.Sobolev.NestedBallCutoff
import OAI.Geometry.RCD.Metric.MeasuredBallLaw

namespace OAI

/-! # Compact probability test densities with nearly full ball mass -/

open Set Filter MeasureTheory Metric
open scoped Topology BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates

def euclideanBallDensity {n : ℕ} (x : Euclidean n) (a b : ℝ) (hab : a<b) : Euclidean n →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (nestedBallCutoff x a b)
    (nestedBallCutoff_lipschitz x hab).continuous 1 (fun y => by
      rw [Real.norm_eq_abs,abs_of_nonneg (nestedBallCutoff_bounds x a b y).1]
      exact (nestedBallCutoff_bounds x a b y).2)

theorem euclideanBallDensity_integrable {n : ℕ} (x : Euclidean n) {a b : ℝ} (hab : a<b) :
    Integrable (euclideanBallDensity x a b hab) volume :=
  (nestedBallCutoff_lipschitz x hab).continuous.integrable_of_hasCompactSupport
    (nestedBallCutoff_hasCompactSupport x hab)

theorem euclideanBallDensity_norm_le {n : ℕ} (x : Euclidean n) {a b : ℝ} (hab : a<b) :
    ‖euclideanBallDensity x a b hab‖≤1 := by
  apply (BoundedContinuousFunction.norm_le (by norm_num : (0:ℝ)≤1)).mpr
  intro y
  change ‖nestedBallCutoff x a b y‖≤1
  rw [Real.norm_eq_abs,abs_of_nonneg (nestedBallCutoff_bounds x a b y).1]
  exact (nestedBallCutoff_bounds x a b y).2

theorem euclideanBallDensity_mass_lower {n : ℕ} (x : Euclidean n) {a b : ℝ} (hab : a<b) :
    volume.real (ball x a)≤∫ y, euclideanBallDensity x a b hab y := by
  have hi := euclideanBallDensity_integrable x hab
  have he : (∫ y in ball x a, euclideanBallDensity x a b hab y)=volume.real (ball x a) := by
    calc _ = ∫ _ in ball x a, (1:ℝ) := setIntegral_congr_fun measurableSet_ball (fun y hy =>
        nestedBallCutoff_eq_one x hab (by
          have hd : dist x y<a := by simpa only [mem_ball,dist_comm] using hy
          exact hd.le))
      _ = _ := by simp
  rw [← he]
  exact integral_mono_measure Measure.restrict_le_self
    (Eventually.of_forall fun y => (nestedBallCutoff_bounds x a b y).1) hi

end RegularPointCoordinates

end

end OAI
