import Mathlib

namespace OAI

/-! Conjugation by a positive contractive approximate unit. This permits
closed conjugation cones to recover their unconjugated generators even in
a nonunital algebra. -/

noncomputable section
open Filter Topology

namespace WeakPureInfiniteness

variable {D : Type*} [NonUnitalCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

lemma approximateUnit_conjugation_tendsto (z : D) :
    Tendsto (fun e : D => star e * z * e) (CStarAlgebra.approximateUnit D) (𝓝 z) := by
  have hf := CStarAlgebra.increasingApproximateUnit D
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hl := Metric.tendsto_nhds.mp (hf.tendsto_mul_right z) (ε / 2) (by positivity)
  have hr := Metric.tendsto_nhds.mp (hf.tendsto_mul_left z) (ε / 2) (by positivity)
  filter_upwards [hf.eventually_norm, hf.eventually_star_eq, hl, hr] with e hen hes hl hr
  rw [dist_eq_norm, hes]
  have he : e * z * e - z = (e * z - z) * e + (z * e - z) := by noncomm_ring
  rw [he]
  simp only [dist_eq_norm] at hl hr
  calc
    _ ≤ ‖(e * z - z) * e‖ + ‖z * e - z‖ := norm_add_le _ _
    _ ≤ ‖e * z - z‖ + ‖z * e - z‖ := by
      apply add_le_add _ le_rfl
      exact (norm_mul_le _ _).trans (by nlinarith [norm_nonneg (e * z - z)])
    _ < ε / 2 + ε / 2 := add_lt_add hl hr
    _ = ε := by ring

lemma continuous_functional_nonneg_of_conjugates (φ : D →L[ℂ] ℂ) (z : D)
    (h : ∀ d : D, 0 ≤ (φ (star d * z * d)).re) : 0 ≤ (φ z).re := by
  have ht := (Complex.continuous_re.comp φ.continuous).continuousAt.tendsto.comp
    (approximateUnit_conjugation_tendsto z)
  exact ge_of_tendsto ht (Filter.Eventually.of_forall h)

omit [PartialOrder D] [StarOrderedRing D] in
lemma isClosed_functional_conjugate_nonneg (φ : D →L[ℂ] ℂ) (z : D) :
    IsClosed {d : D | 0 ≤ (φ (star d * z * d)).re} := by
  exact isClosed_le continuous_const
    (Complex.continuous_re.comp (φ.continuous.comp
      ((continuous_star.mul continuous_const).mul continuous_id)))

end WeakPureInfiniteness

end

end OAI
