import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.MeasureBounds

namespace OAI

/-!
# Coefficient bounds from separation from a span

Distance to a subspace is the norm of the orthogonal component. A positive
lower bound for that distance controls the coefficient of an added vector,
and extends an existing coordinate bound to the enlarged family.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Module EuclideanGeometry
open scoped BigOperators

theorem euclidean_starProjection_norm_le {d : ℕ}
    (S : Submodule ℝ (Ambient d)) (x : Ambient d) : ‖S.starProjection x‖ ≤ ‖x‖ :=
  S.norm_starProjection_apply_le x

theorem submodule_infDist_eq_normal_projection {d : ℕ}
    (S : Submodule ℝ (Ambient d)) (x : Ambient d) :
    infDist x (S : Set (Ambient d)) = ‖Sᗮ.starProjection x‖ := by
  let : Nonempty S.toAffineSubspace := ⟨0, S.zero_mem⟩
  have hp : (orthogonalProjection S.toAffineSubspace x : Ambient d) = S.starProjection x := by
    simpa only [Submodule.toAffineSubspace_direction, vsub_eq_sub, sub_zero,
      vadd_eq_add, add_zero, Submodule.coe_orthogonalProjectionOnto_apply] using!
      orthogonalProjection_apply_mem S.toAffineSubspace S.zero_mem (p := x)
  change infDist x (S.toAffineSubspace : Set (Ambient d)) = _
  rw [← dist_orthogonalProjection_eq_infDist S.toAffineSubspace x, hp, dist_eq_norm]
  have h := S.starProjection_add_starProjection_orthogonal x
  have hx : x - S.starProjection x = Sᗮ.starProjection x := by
    exact sub_eq_iff_eq_add.mpr (h.symm.trans (add_comm _ _))
  rw [hx]

theorem coefficient_bound_of_span_distance {d : ℕ}
    (S : Submodule ℝ (Ambient d)) (p u : Ambient d) (hp : p ∈ S)
    (r : ℝ) (hr : 0 < r) (hu : r ≤ infDist u (S : Set (Ambient d))) (s : ℝ) :
    |s| ≤ ‖p + s • u‖ / r := by
  have hself : S.starProjection p = p := S.starProjection_eq_self_iff.mpr hp
  have hz : Sᗮ.starProjection p = 0 := by
    have h := S.starProjection_add_starProjection_orthogonal p
    rw [hself, add_eq_left] at h
    exact h
  apply (le_div_iff₀ hr).mpr
  calc
    |s| * r ≤ |s| * infDist u (S : Set (Ambient d)) :=
      mul_le_mul_of_nonneg_left hu (abs_nonneg _)
    _ = ‖Sᗮ.starProjection (p + s • u)‖ := by
      rw [submodule_infDist_eq_normal_projection, map_add, map_smul, hz, zero_add,
        norm_smul, Real.norm_eq_abs]
    _ ≤ _ := euclidean_starProjection_norm_le Sᗮ (p + s • u)

theorem coordinate_bound_extend {n d : ℕ} (v : Fin n → Ambient d) (u : Ambient d)
    (C M r : ℝ) (hC : 0 ≤ C) (hM : ‖u‖ ≤ M) (hr : 0 < r)
    (hsep : r ≤ infDist u (Submodule.span ℝ (range v) : Set (Ambient d)))
    (hprefix : ∀ t : Fin n → ℝ, (∑ i, |t i|) ≤ C * ‖∑ i, t i • v i‖)
    (t : Fin n → ℝ) (s : ℝ) :
    (∑ i, |t i|) + |s| ≤
      (C * (1 + M / r) + 1 / r) * ‖(∑ i, t i • v i) + s • u‖ := by
  let p : Ambient d := ∑ i, t i • v i
  have hp : p ∈ Submodule.span ℝ (range v) := by
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span (mem_range_self i)))
  have hs : |s| ≤ ‖p + s • u‖ / r :=
    coefficient_bound_of_span_distance (Submodule.span ℝ (range v)) p u hp r hr hsep s
  have hM0 : 0 ≤ M := (norm_nonneg u).trans hM
  have hpnorm : ‖p‖ ≤ (1 + M / r) * ‖p + s • u‖ := by
    calc
      _ = ‖(p + s • u) - s • u‖ := by rw [add_sub_cancel_right]
      _ ≤ ‖p + s • u‖ + ‖s • u‖ := norm_sub_le _ _
      _ = ‖p + s • u‖ + |s| * ‖u‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ ‖p + s • u‖ + (‖p + s • u‖ / r) * M := by
        apply add_le_add le_rfl
        exact (mul_le_mul_of_nonneg_left hM (abs_nonneg s)).trans
          (mul_le_mul_of_nonneg_right hs hM0)
      _ = _ := by ring
  calc
    _ ≤ C * ‖p‖ + |s| := add_le_add (hprefix t) le_rfl
    _ ≤ C * ((1 + M / r) * ‖p + s • u‖) + ‖p + s • u‖ / r :=
      add_le_add (mul_le_mul_of_nonneg_left hpnorm hC) hs
    _ = _ := by ring

end

end RieszRectifiability

end OAI
