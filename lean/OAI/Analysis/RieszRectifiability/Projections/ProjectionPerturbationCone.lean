import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.MeasureBounds

namespace OAI

/-!
Small errors from an orthogonal projection give quantitative bounds on the parallel and
perpendicular components, keeping perturbed vectors in a controlled cone.
-/

namespace RieszRectifiability

noncomputable section

open Metric Set

theorem projection_perturbation_vector_bounds {d : ℕ}
    (P : Submodule ℝ (Ambient d)) (v w : Ambient d) (η : ℝ)
    (hη : 0 ≤ η) (hηsmall : η ≤ 1 / 4)
    (hv : ‖v‖ ≤ 2 * ‖P.starProjection v‖)
    (herr : ‖w - P.starProjection v‖ ≤ η * ‖v‖) :
    ‖v‖ ≤ 4 * ‖P.starProjection w‖ ∧
      ‖(Pᗮ : Submodule ℝ (Ambient d)).starProjection w‖ ≤
        (4 * η) * ‖P.starProjection w‖ ∧
      ‖w‖ ≤ (1 + η) * ‖v‖ ∧
      ‖w‖ ≤ (1 + 4 * η) * ‖P.starProjection w‖ := by
  have hPv : P.starProjection v ∈ P := (P.orthogonalProjectionOnto v).property
  have hself : P.starProjection (P.starProjection v) = P.starProjection v :=
    P.starProjection_eq_self_iff.mpr hPv
  have hperp : (Pᗮ : Submodule ℝ (Ambient d)).starProjection (P.starProjection v) = 0 := by
    rw [P.starProjection_orthogonal_val, hself, sub_self]
  have hparallel : ‖P.starProjection w - P.starProjection v‖ ≤ η * ‖v‖ := by
    have h := (P.norm_starProjection_apply_le (w - P.starProjection v)).trans herr
    rwa [map_sub, hself] at h
  have hbase : ‖P.starProjection v‖ ≤ ‖P.starProjection w‖ + η * ‖v‖ := by
    have htri := norm_sub_le (P.starProjection w)
      (P.starProjection w - P.starProjection v)
    rw [sub_sub_cancel] at htri
    linarith
  have hinverse : ‖v‖ ≤ 4 * ‖P.starProjection w‖ := by
    have hm := mul_le_mul_of_nonneg_right hηsmall (norm_nonneg v)
    linarith
  have hnormal : ‖(Pᗮ : Submodule ℝ (Ambient d)).starProjection w‖ ≤ η * ‖v‖ := by
    have h := ((Pᗮ : Submodule ℝ (Ambient d)).norm_starProjection_apply_le
      (w - P.starProjection v)).trans herr
    rwa [map_sub, hperp, sub_zero] at h
  have hcone : ‖(Pᗮ : Submodule ℝ (Ambient d)).starProjection w‖ ≤
      (4 * η) * ‖P.starProjection w‖ := by
    have hm := mul_le_mul_of_nonneg_left hinverse hη
    nlinarith
  have hforward : ‖w‖ ≤ (1 + η) * ‖v‖ := by
    have htri := norm_add_le (w - P.starProjection v) (P.starProjection v)
    rw [sub_add_cancel] at htri
    have hproj := P.norm_starProjection_apply_le v
    nlinarith
  have himage : ‖w‖ ≤ (1 + 4 * η) * ‖P.starProjection w‖ := by
    have htri := norm_add_le (P.starProjection w)
      ((Pᗮ : Submodule ℝ (Ambient d)).starProjection w)
    rw [P.starProjection_add_starProjection_orthogonal] at htri
    nlinarith
  exact ⟨hinverse, hcone, hforward, himage⟩

theorem projection_perturbation_injOn {d : ℕ}
    (P : Submodule ℝ (Ambient d)) (E : Set (Ambient d)) (f : Ambient d → Ambient d)
    (η : ℝ) (hη : 0 ≤ η) (hηsmall : η ≤ 1 / 4)
    (hinput : ∀ x ∈ E, ∀ y ∈ E,
      dist x y ≤ 2 * dist (P.starProjection x) (P.starProjection y))
    (herr : ∀ x ∈ E, ∀ y ∈ E,
      ‖(f x - f y) - P.starProjection (x - y)‖ ≤ η * dist x y) : Set.InjOn f E := by
  intro x hx y hy hxy
  have hv : ‖x - y‖ ≤ 2 * ‖P.starProjection (x - y)‖ := by
    simpa only [map_sub, dist_eq_norm] using! hinput x hx y hy
  have h := (projection_perturbation_vector_bounds P (x - y) (f x - f y) η
    hη hηsmall hv (herr x hx y hy)).1
  rw [hxy, sub_self, map_zero, norm_zero, mul_zero] at h
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))

theorem projection_perturbation_image_cone {d : ℕ}
    (P : Submodule ℝ (Ambient d)) (E : Set (Ambient d)) (f : Ambient d → Ambient d)
    (η : ℝ) (hη : 0 ≤ η) (hηsmall : η ≤ 1 / 4)
    (hinput : ∀ x ∈ E, ∀ y ∈ E,
      dist x y ≤ 2 * dist (P.starProjection x) (P.starProjection y))
    (herr : ∀ x ∈ E, ∀ y ∈ E,
      ‖(f x - f y) - P.starProjection (x - y)‖ ≤ η * dist x y) :
    ∀ u ∈ f '' E, ∀ v ∈ f '' E,
      ‖(Pᗮ : Submodule ℝ (Ambient d)).starProjection (u - v)‖ ≤
        (4 * η) * dist (P.starProjection u) (P.starProjection v) := by
  rintro u ⟨x, hx, rfl⟩ v ⟨y, hy, rfl⟩
  have hv : ‖x - y‖ ≤ 2 * ‖P.starProjection (x - y)‖ := by
    simpa only [map_sub, dist_eq_norm] using! hinput x hx y hy
  have h := (projection_perturbation_vector_bounds P (x - y) (f x - f y) η
    hη hηsmall hv (herr x hx y hy)).2.1
  simpa only [map_sub, dist_eq_norm] using! h

end

end RieszRectifiability

end OAI
