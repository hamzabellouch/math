import OAI.Geometry.RCD.Heat.BoundedHeatOrder

namespace OAI

/-! # Pointwise control of uniformly Lipschitz L² representatives

Small L² mass prevents a fixed nonzero value from persisting on a ball of
positive measure. Applied to bounded heat data, this turns L² convergence
into pointwise convergence without presupposing a kernel bound.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X)

/-- A value separated from zero forces explicit L² mass on a metric ball. -/
theorem lipschitz_value_sq_mass (u : Lp ℝ 2 μ) (v : X → ℝ)
    (hu : u =ᵐ[μ] v) (L : ℝ≥0) (hv : LipschitzWith L v)
    (x : X) {r a : ℝ} (hfinite : μ (ball x r) ≠ ∞) (ha : 0 ≤ a) (hvalue : a + L * r ≤ |v x|) :
    a ^ 2 * μ.real (ball x r) ≤ ‖u‖ ^ 2 := by
  have hval (y : X) (hy : y ∈ ball x r) : a ≤ |v y| := by
    have hLip := hv.dist_le_mul x y
    rw [Real.dist_eq, dist_comm x y] at hLip
    have htri := abs_sub_abs_le_abs_sub (v x) (v y)
    have hdist : dist y x ≤ r := hy.le
    have hm := mul_le_mul_of_nonneg_left hdist L.coe_nonneg
    linarith
  have hi := (Lp.memLp u).integrable_sq
  have hbounded : (∫ y in ball x r, a ^ 2 ∂μ) ≤
      ∫ y in ball x r, (u y) ^ 2 ∂μ := by
    have : IsFiniteMeasure (μ.restrict (ball x r)) := ⟨by simpa using hfinite.lt_top⟩
    apply integral_mono_ae (integrable_const _) hi.integrableOn
    filter_upwards [ae_restrict_mem measurableSet_ball, ae_restrict_of_ae hu] with y hy he
    rw [he]
    exact (sq_le_sq₀ ha (abs_nonneg _)).mpr (hval y hy) |>.trans_eq (sq_abs _)
  calc
    _ = ∫ y in ball x r, a ^ 2 ∂μ := by simp [mul_comm]
    _ ≤ ∫ y in ball x r, (u y) ^ 2 ∂μ := hbounded
    _ ≤ ∫ y, (u y) ^ 2 ∂μ :=
      setIntegral_le_integral hi (Eventually.of_forall fun y => sq_nonneg _)
    _ = ‖u‖ ^ 2 := integral_sq_Lp μ u

end RegularPointCoordinates

end

end OAI
