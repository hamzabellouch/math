import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.KernelBasic
import OAI.Analysis.RieszRectifiability.Kernel.LeastSquaredExcess

namespace OAI

/-!
# Transfer of squared plane-distance moments

A pointwise comparison of distances to two affine planes yields a comparison
of their second moments on a ball. The additive distance error contributes its
square times the ball mass, using local finiteness to justify integration.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

theorem plane_distance_second_moment_transfer {d : ℕ}
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ]
    (S W : AffineSubspace ℝ (Ambient d))
    (hS : (S : Set (Ambient d)).Nonempty) (hW : (W : Set (Ambient d)).Nonempty)
    (R t : ℝ) (ht : 0 ≤ t)
    (hpoint : ∀ x ∈ ball (0 : Ambient d) R,
      infDist x (S : Set (Ambient d)) ≤ infDist x (W : Set (Ambient d)) + t) :
    (∫ x in ball (0 : Ambient d) R, infDist x (S : Set (Ambient d)) ^ 2 ∂μ) ≤
      2 * (∫ x in ball (0 : Ambient d) R, infDist x (W : Set (Ambient d)) ^ 2 ∂μ) +
        2 * t ^ 2 * μ.real (ball (0 : Ambient d) R) := by
  have : IsFiniteMeasure (μ.restrict (ball (0 : Ambient d) R)) := isFiniteMeasure_restrict.mpr
    (ne_of_lt ((measure_mono ball_subset_closedBall).trans_lt
      (isCompact_closedBall (0 : Ambient d) R).measure_lt_top))
  have hSi := squared_infDist_integrableOn_ball μ 0 R S hS
  have hWi := squared_infDist_integrableOn_ball μ 0 R W hW
  have hbound : (∫ x in ball (0 : Ambient d) R, infDist x (S : Set (Ambient d)) ^ 2 ∂μ) ≤
      ∫ x in ball (0 : Ambient d) R, 2 * infDist x (W : Set (Ambient d)) ^ 2 + 2 * t ^ 2 ∂μ := by
    apply integral_mono_ae hSi ((hWi.const_mul 2).add (integrable_const _))
    filter_upwards [ae_restrict_mem (μ := μ) measurableSet_ball] with x hx
    change infDist x (S : Set (Ambient d)) ^ 2 ≤ 2 * infDist x (W : Set (Ambient d)) ^ 2 + 2 * t ^ 2
    have hsq := (sq_le_sq₀ infDist_nonneg (add_nonneg infDist_nonneg ht)).mpr (hpoint x hx)
    nlinarith [sq_nonneg (infDist x (W : Set (Ambient d)) - t)]
  calc
    _ ≤ ∫ x in ball (0 : Ambient d) R, 2 * infDist x (W : Set (Ambient d)) ^ 2 + 2 * t ^ 2 ∂μ := hbound
    _ = _ := by
      rw [integral_add (hWi.const_mul 2) (integrable_const _), integral_const_mul, integral_const]
      simp only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul]
      ring

theorem plane_second_moment_bound_from_distance_transfer {n d : ℕ}
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ]
    (C : ℝ) (hg : GlobalUpperGrowth n C μ)
    (S W : AffineSubspace ℝ (Ambient d))
    (hS : (S : Set (Ambient d)).Nonempty) (hW : (W : Set (Ambient d)).Nonempty)
    (R E K D : ℝ) (hR : 0 < R) (hE : 0 ≤ E) (hK : 0 ≤ K)
    (hfit : (∫ x in ball (0 : Ambient d) R, infDist x (W : Set (Ambient d)) ^ 2 ∂μ) ≤
      D * E ^ 2 * R ^ (n + 2))
    (hpoint : ∀ x ∈ ball (0 : Ambient d) R,
      infDist x (S : Set (Ambient d)) ≤ infDist x (W : Set (Ambient d)) + K * E * R) :
    (∫ x in ball (0 : Ambient d) R, infDist x (S : Set (Ambient d)) ^ 2 ∂μ) ≤
      (2 * D + 2 * C * K ^ 2) * E ^ 2 * R ^ (n + 2) := by
  have hm : μ.real (ball (0 : Ambient d) R) ≤ C * R ^ n :=
    ENNReal.toReal_le_of_le_ofReal (mul_nonneg hg.1 (pow_nonneg hR.le n)) (hg.2 0 R hR)
  calc
    _ ≤ 2 * (∫ x in ball (0 : Ambient d) R, infDist x (W : Set (Ambient d)) ^ 2 ∂μ) +
        2 * (K * E * R) ^ 2 * μ.real (ball (0 : Ambient d) R) :=
      plane_distance_second_moment_transfer μ S W hS hW R (K * E * R) (by positivity) hpoint
    _ ≤ 2 * (D * E ^ 2 * R ^ (n + 2)) + 2 * (K * E * R) ^ 2 * (C * R ^ n) :=
      add_le_add (mul_le_mul_of_nonneg_left hfit (by norm_num))
        (mul_le_mul_of_nonneg_left hm (by positivity))
    _ = _ := by rw [pow_add R n 2]; ring

end

end RieszRectifiability

end OAI
