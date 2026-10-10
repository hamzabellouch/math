import Mathlib
import OAI.Analysis.RieszRectifiability.Flatness.ApproximatePlaneFits

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem exists_dyadic_approximate_fits {n d : ℕ} (hnd : n ≤ d)
    (μ : Measure (Ambient d)) (δ b : ℝ) (hδ : 0 < δ) (hb : 0 < b) (N : ℕ)
    (hexcess : ∀ i ≤ N, squaredExcess n μ 0 ((2 : ℝ) ^ i) ≤ (δ * b ^ i) ^ 2) :
    ∃ P : ℕ → AffineSubspace ℝ (Ambient d), (∀ i, IsAffineNPlane n (P i)) ∧
      ∀ i ≤ N, (∫ x in ball (0 : Ambient d) ((2 : ℝ) ^ i),
        infDist x (P i : Set (Ambient d)) ^ 2 ∂μ) ≤
          2 * (δ * b ^ i) ^ 2 * ((2 : ℝ) ^ i) ^ (n + 2) := by
  have hfit : ∀ i : ℕ, ∃ S : AffineSubspace ℝ (Ambient d), IsAffineNPlane n S ∧
      quadraticPlaneError n μ 0 ((2 : ℝ) ^ i) S <
        squaredExcess n μ 0 ((2 : ℝ) ^ i) + (δ * b ^ i) ^ 2 := by
    intro i
    exact exists_approximate_plane_fit hnd μ 0 ((2 : ℝ) ^ i) ((δ * b ^ i) ^ 2)
      (sq_pos_of_pos (mul_pos hδ (pow_pos hb i)))
  choose P hP herr using hfit
  refine ⟨P, hP, ?_⟩
  intro i hi
  have hnorm : quadraticPlaneError n μ 0 ((2 : ℝ) ^ i) (P i) ≤ 2 * (δ * b ^ i) ^ 2 :=
    (herr i).le.trans (by linarith [hexcess i hi])
  rw [← quadraticPlaneError_integral_identity μ 0 ((2 : ℝ) ^ i) (by positivity) (P i)]
  calc
    ((2 : ℝ) ^ i) ^ (n + 2) * quadraticPlaneError n μ 0 ((2 : ℝ) ^ i) (P i) ≤
        ((2 : ℝ) ^ i) ^ (n + 2) * (2 * (δ * b ^ i) ^ 2) :=
      mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = _ := by ring

end

end RieszRectifiability

end OAI
