import OAI.MeasureTheory.Falconer.Angular.SphereCapBound
import OAI.MeasureTheory.Falconer.Geometry.EuclideanRieszEnergy

namespace OAI

/-! Uniform subcritical potentials of the actual Euclidean surface measure. -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal

theorem surfaceMeasure_frostman (n : ℕ) :
    FrostmanBallBound (surfaceMeasure (n+1)) (n : ℝ)
      ((((n+1 : ℕ) : ℝ)*2^(n+1))*2^n) := by
  intro x r hr
  rw [surfaceMeasure, Measure.map_apply measurable_subtype_coe measurableSet_ball]
  by_cases h : ((Subtype.val : Sphere (n+1) → Space (n+1)) ⁻¹' ball x r).Nonempty
  · obtain ⟨w, hw⟩ := h
    have hsub : ((Subtype.val : Sphere (n+1) → Space (n+1)) ⁻¹' ball x r) ⊆
        ball w (2*r) := by
      intro z hz
      change dist (z : Space (n+1)) x < r at hz
      change dist (w : Space (n+1)) x < r at hw
      change dist z w < 2*r
      rw [Subtype.dist_eq]
      exact (dist_triangle (z : Space (n+1)) x w).trans_lt
        (by rw [dist_comm x (w : Space (n+1))]; linarith)
    calc
      _ ≤ sphereMeasure (n+1) (ball w (2*r)) := measure_mono hsub
      _ ≤ ENNReal.ofReal (((n+1 : ℕ) : ℝ)*2^(n+1)*(2*r)^n) :=
        sphere_cap_bound n w (by positivity)
      _ = _ := by rw [Real.rpow_natCast, mul_pow]; congr 1; ring
  · rw [Set.not_nonempty_iff_eq_empty.mp h, measure_empty]
    exact bot_le

theorem surface_potential_uniform_bound (n : ℕ) {s : ℝ} (hs : 0 < s) (hsn : s < n) :
    ∃ B : ℝ≥0∞, B < ∞ ∧ ∀ x : Space (n+1),
      (∫⁻ y : Space (n+1), (edist x y)^(-s) ∂surfaceMeasure (n+1)) ≤ B :=
  euclidean_riesz_potential_uniform_bound (surfaceMeasure (n+1)) hs hsn
    (surfaceMeasure_frostman n)

end Falconer

end OAI
