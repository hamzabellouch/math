import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.OrderedSpanConditioning

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set EuclideanGeometry
open scoped BigOperators

theorem linear_combination_perturbation_bound {n d : ℕ}
    (v w : Fin n → Ambient d) (η : ℝ) (hclose : ∀ i, ‖w i - v i‖ ≤ η)
    (t : Fin n → ℝ) :
    ‖(∑ i, t i • v i) - ∑ i, t i • w i‖ ≤ η * ∑ i, |t i| := by
  rw [← Finset.sum_sub_distrib]
  simp only [← smul_sub]
  calc
    _ ≤ ∑ i, ‖t i • (v i - w i)‖ := norm_sum_le _ _
    _ ≤ ∑ i, |t i| * η := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, Real.norm_eq_abs, norm_sub_rev]
      exact mul_le_mul_of_nonneg_left (hclose i) (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring

theorem coordinate_bound_under_perturbation {n d : ℕ}
    (v w : Fin n → Ambient d) (C η : ℝ) (hC : 0 ≤ C)
    (hsmall : C * η ≤ 1 / 2) (hclose : ∀ i, ‖w i - v i‖ ≤ η)
    (hbound : ∀ t : Fin n → ℝ, (∑ i, |t i|) ≤ C * ‖∑ i, t i • v i‖)
    (t : Fin n → ℝ) :
    (∑ i, |t i|) ≤ (2 * C) * ‖∑ i, t i • w i‖ := by
  have hnorm : ‖∑ i, t i • v i‖ ≤
      ‖∑ i, t i • w i‖ + η * ∑ i, |t i| := by
    calc
      _ = ‖(∑ i, t i • w i) + ((∑ i, t i • v i) - ∑ i, t i • w i)‖ := by
        congr 1
        abel
      _ ≤ ‖∑ i, t i • w i‖ + ‖(∑ i, t i • v i) - ∑ i, t i • w i‖ := norm_add_le _ _
      _ ≤ _ := add_le_add le_rfl (linear_combination_perturbation_bound v w η hclose t)
  have h := (hbound t).trans (mul_le_mul_of_nonneg_left hnorm hC)
  have hs : 0 ≤ ∑ i, |t i| := Finset.sum_nonneg (fun i _ => abs_nonneg (t i))
  have hp := mul_le_mul_of_nonneg_right hsmall hs
  nlinarith

theorem linearIndependent_under_small_perturbation {n d : ℕ}
    (v w : Fin n → Ambient d) (C η : ℝ) (hC : 0 ≤ C)
    (hsmall : C * η ≤ 1 / 2) (hclose : ∀ i, ‖w i - v i‖ ≤ η)
    (hbound : ∀ t : Fin n → ℝ, (∑ i, |t i|) ≤ C * ‖∑ i, t i • v i‖) :
    LinearIndependent ℝ w :=
  linearIndependent_of_coordinate_bound w (2 * C)
    (coordinate_bound_under_perturbation v w C η hC hsmall hclose hbound)

theorem projected_anchor_perturbation_bound {d : ℕ}
    (S : AffineSubspace ℝ (Ambient d)) [Nonempty S] (p₀ p : Ambient d) :
    ‖((orthogonalProjection S p : Ambient d) - (orthogonalProjection S p₀ : Ambient d)) -
      (p - p₀)‖ ≤ infDist p (S : Set (Ambient d)) + infDist p₀ (S : Set (Ambient d)) := by
  calc
    _ = ‖((orthogonalProjection S p : Ambient d) - p) -
      ((orthogonalProjection S p₀ : Ambient d) - p₀)‖ := by congr 1; abel
    _ ≤ ‖(orthogonalProjection S p : Ambient d) - p‖ +
      ‖(orthogonalProjection S p₀ : Ambient d) - p₀‖ := norm_sub_le _ _
    _ = _ := by
      rw [← dist_eq_norm, ← dist_eq_norm, dist_comm (orthogonalProjection S p : Ambient d) p,
        dist_comm (orthogonalProjection S p₀ : Ambient d) p₀,
        dist_orthogonalProjection_eq_infDist, dist_orthogonalProjection_eq_infDist]

end

end RieszRectifiability

end OAI
