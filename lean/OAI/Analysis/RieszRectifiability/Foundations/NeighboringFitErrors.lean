import Mathlib
import OAI.Analysis.RieszRectifiability.Flatness.JointPlaneGoodSet

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

def dyadicFitErrorConstant (n : ℕ) (b : ℝ) : ℝ := 2 + 2 * (2 : ℝ) ^ (n + 2) * b ^ 2

theorem dyadicFitErrorConstant_pos (n : ℕ) (b : ℝ) : 0 < dyadicFitErrorConstant n b := by
  dsimp only [dyadicFitErrorConstant]
  positivity

theorem neighboring_joint_fit_error_bound {n d : ℕ}
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ]
    (S W : AffineSubspace ℝ (Ambient d))
    (hS : (S : Set (Ambient d)).Nonempty) (hW : (W : Set (Ambient d)).Nonempty)
    (R E b : ℝ) (hR : 0 ≤ R)
    (hleft : (∫ x in ball (0 : Ambient d) R, infDist x (S : Set (Ambient d)) ^ 2 ∂μ) ≤
      2 * E ^ 2 * R ^ (n + 2))
    (hright : (∫ x in ball (0 : Ambient d) (2 * R), infDist x (W : Set (Ambient d)) ^ 2 ∂μ) ≤
      2 * (b * E) ^ 2 * (2 * R) ^ (n + 2)) :
    (∫ x in ball (0 : Ambient d) R, jointPlaneFitError S W x ∂μ) ≤
      dyadicFitErrorConstant n b * E ^ 2 * R ^ (n + 2) := by
  have hSi := squared_infDist_integrableOn_ball μ 0 R S hS
  have hWi := squared_infDist_integrableOn_ball μ 0 R W hW
  have hWlarge := squared_infDist_integrableOn_ball μ 0 (2 * R) W hW
  have hrestrict : (∫ x in ball (0 : Ambient d) R, infDist x (W : Set (Ambient d)) ^ 2 ∂μ) ≤
      ∫ x in ball (0 : Ambient d) (2 * R), infDist x (W : Set (Ambient d)) ^ 2 ∂μ :=
    integral_mono_measure (Measure.restrict_mono (ball_subset_ball (by linarith)) le_rfl)
      (Filter.Eventually.of_forall (fun x => sq_nonneg (infDist x (W : Set (Ambient d))))) hWlarge
  change (∫ x in ball (0 : Ambient d) R,
    infDist x (S : Set (Ambient d)) ^ 2 + infDist x (W : Set (Ambient d)) ^ 2 ∂μ) ≤ _
  rw [integral_add hSi hWi]
  calc
    _ ≤ 2 * E ^ 2 * R ^ (n + 2) + 2 * (b * E) ^ 2 * (2 * R) ^ (n + 2) :=
      add_le_add hleft (hrestrict.trans hright)
    _ = _ := by simp only [dyadicFitErrorConstant, mul_pow]; ring

theorem dyadic_neighboring_joint_fit_error_bound {n d : ℕ}
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ]
    (P : ℕ → AffineSubspace ℝ (Ambient d)) (hP : ∀ i, IsAffineNPlane n (P i))
    (δ b : ℝ) (N : ℕ)
    (hfit : ∀ i ≤ N, (∫ x in ball (0 : Ambient d) ((2 : ℝ) ^ i),
      infDist x (P i : Set (Ambient d)) ^ 2 ∂μ) ≤
        2 * (δ * b ^ i) ^ 2 * ((2 : ℝ) ^ i) ^ (n + 2)) (i : ℕ) (hi : i < N) :
    (∫ x in ball (0 : Ambient d) ((2 : ℝ) ^ i), jointPlaneFitError (P i) (P (i + 1)) x ∂μ) ≤
      dyadicFitErrorConstant n b * (δ * b ^ i) ^ 2 * ((2 : ℝ) ^ i) ^ (n + 2) := by
  apply neighboring_joint_fit_error_bound μ (P i) (P (i + 1)) (hP i).1 (hP (i + 1)).1
    ((2 : ℝ) ^ i) (δ * b ^ i) b (by positivity) (hfit i hi.le)
  have hright := hfit (i + 1) (Nat.succ_le_of_lt hi)
  have hr : (2 : ℝ) ^ (i + 1) = 2 * (2 : ℝ) ^ i := by rw [pow_succ]; ring
  have he : δ * b ^ (i + 1) = b * (δ * b ^ i) := by rw [pow_succ]; ring
  rw [hr, he] at hright
  exact hright

end

end RieszRectifiability

end OAI
