import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.MeasureBounds

namespace OAI

namespace RieszRectifiability

noncomputable section

open Metric Set
open scoped NNReal

theorem projection_cone_transfer_vector {d : ℕ}
    (P Q : Submodule ℝ (Ambient d)) (L α : ℝ≥0)
    (hsmall : (L : ℝ) + (α : ℝ) ≤ 1 / 2)
    (hop : ‖P.starProjection - Q.starProjection‖ ≤ (α : ℝ))
    (v : Ambient d)
    (hcone : ‖(Pᗮ : Submodule ℝ (Ambient d)).starProjection v‖ ≤ (L : ℝ) * ‖P.starProjection v‖) :
    ‖v‖ ≤ 2 * ‖Q.starProjection v‖ ∧
      ‖(Qᗮ : Submodule ℝ (Ambient d)).starProjection v‖ ≤
        (2 * ((L : ℝ) + (α : ℝ))) * ‖Q.starProjection v‖ := by
  have hdiff : ‖P.starProjection v - Q.starProjection v‖ ≤ (α : ℝ) * ‖v‖ :=
    ((P.starProjection - Q.starProjection).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right hop (norm_nonneg v))
  have hid : (Qᗮ : Submodule ℝ (Ambient d)).starProjection v =
      (Pᗮ : Submodule ℝ (Ambient d)).starProjection v +
        (P.starProjection v - Q.starProjection v) := by
    rw [Q.starProjection_orthogonal_val, P.starProjection_orthogonal_val]
    abel
  have hnormal : ‖(Qᗮ : Submodule ℝ (Ambient d)).starProjection v‖ ≤
      ((L : ℝ) + (α : ℝ)) * ‖v‖ := by
    rw [hid]
    calc
      _ ≤ ‖(Pᗮ : Submodule ℝ (Ambient d)).starProjection v‖ +
          ‖P.starProjection v - Q.starProjection v‖ := norm_add_le _ _
      _ ≤ (L : ℝ) * ‖P.starProjection v‖ + (α : ℝ) * ‖v‖ := add_le_add hcone hdiff
      _ ≤ (L : ℝ) * ‖v‖ + (α : ℝ) * ‖v‖ :=
        add_le_add (mul_le_mul_of_nonneg_left (P.norm_starProjection_apply_le v) L.coe_nonneg) le_rfl
      _ = _ := by ring
  have hinverse : ‖v‖ ≤ 2 * ‖Q.starProjection v‖ := by
    have htri := norm_add_le (Q.starProjection v)
      ((Qᗮ : Submodule ℝ (Ambient d)).starProjection v)
    rw [Q.starProjection_add_starProjection_orthogonal] at htri
    have hm := mul_le_mul_of_nonneg_right hsmall (norm_nonneg v)
    linarith
  refine ⟨hinverse, ?_⟩
  have hm := mul_le_mul_of_nonneg_left hinverse (add_nonneg L.coe_nonneg α.coe_nonneg)
  nlinarith

theorem projection_cone_transfer {d : ℕ}
    (P Q : Submodule ℝ (Ambient d)) (A : Set (Ambient d)) (L α : ℝ≥0)
    (hsmall : (L : ℝ) + (α : ℝ) ≤ 1 / 2)
    (hop : ‖P.starProjection - Q.starProjection‖ ≤ (α : ℝ))
    (hcone : ∀ x ∈ A, ∀ y ∈ A,
      ‖(Pᗮ : Submodule ℝ (Ambient d)).starProjection (x - y)‖ ≤
        (L : ℝ) * dist (P.starProjection x) (P.starProjection y)) :
    ∀ x ∈ A, ∀ y ∈ A,
      ‖(Qᗮ : Submodule ℝ (Ambient d)).starProjection (x - y)‖ ≤
        (2 * ((L : ℝ) + (α : ℝ))) * dist (Q.starProjection x) (Q.starProjection y) := by
  intro x hx y hy
  have hp : ‖(Pᗮ : Submodule ℝ (Ambient d)).starProjection (x - y)‖ ≤
      (L : ℝ) * ‖P.starProjection (x - y)‖ := by
    simpa only [map_sub, dist_eq_norm] using! hcone x hx y hy
  have h := (projection_cone_transfer_vector P Q L α hsmall hop (x - y) hp).2
  simpa only [map_sub, dist_eq_norm] using! h

end

end RieszRectifiability

end OAI
