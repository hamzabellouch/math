import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.DyadicChainPropagation

namespace OAI

/-!
# Support tubes and initial excess bounds

A support tube of width `η` around an affine `n`-plane bounds the normalized
squared excess on a ball of radius `R` by `G * (η / R) ^ 2` under global upper
growth. A positive tube threshold therefore seeds the excess estimates on a
finite dyadic horizon, with the same plane serving at every intermediate scale.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem squaredExcess_le_of_support_tube {d : ℕ} (n : ℕ) (G : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth n G μ)
    (a : Ambient d) (R η : ℝ) (hR : 0 < R) (hη : 0 ≤ η)
    (S : AffineSubspace ℝ (Ambient d)) (hS : IsAffineNPlane n S)
    (htube : ∀ x ∈ ball a R, x ∈ μ.support → infDist x (S : Set (Ambient d)) ≤ η) :
    squaredExcess n μ a R ≤ G * (η / R) ^ 2 := by
  let : IsFiniteMeasureOnCompacts μ := globalGrowth_finite_on_compacts G μ hg
  have : IsFiniteMeasure (μ.restrict (ball a R)) := isFiniteMeasure_restrict.mpr
    (ne_of_lt ((measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall a R).measure_lt_top))
  have hi := squared_infDist_integrableOn_ball μ a R S hS.1
  have hb : (∫ x in ball a R, infDist x (S : Set (Ambient d)) ^ 2 ∂μ) ≤
      η ^ 2 * μ.real (ball a R) := by
    calc
      _ ≤ ∫ _x in ball a R, η ^ 2 ∂μ := by
        apply integral_mono_ae hi (integrable_const _)
        filter_upwards [ae_restrict_mem (μ := μ) measurableSet_ball,
          ae_restrict_of_ae μ.support_mem_ae] with x hx hxs
        exact (sq_le_sq₀ infDist_nonneg hη).mpr (htube x hx hxs)
      _ = _ := by
        rw [integral_const]
        simp only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul, mul_comm]
  have hm : μ.real (ball a R) ≤ G * R ^ n :=
    ENNReal.toReal_le_of_le_ofReal (mul_nonneg hg.1 (pow_nonneg hR.le n)) (hg.2 a R hR)
  calc
    _ ≤ quadraticPlaneError n μ a R S := squaredExcess_le_planeError n μ a R hR.le S hS
    _ ≤ (R ^ (n + 2))⁻¹ * (η ^ 2 * (G * R ^ n)) := by
      exact mul_le_mul_of_nonneg_left (hb.trans (mul_le_mul_of_nonneg_left hm (sq_nonneg η)))
        (by positivity)
    _ = _ := by
      rw [pow_add]
      field_simp

theorem exists_positive_tube_threshold (G δ : ℝ) (hG : 0 ≤ G) (hδ : 0 < δ) :
    ∃ α : ℝ, 0 < α ∧ α ≤ δ ∧ G * α ^ 2 ≤ δ ^ 2 := by
  refine ⟨δ / (G + 1), div_pos hδ (by positivity), ?_, ?_⟩
  · apply (div_le_iff₀ (by positivity : 0 < G + 1)).mpr
    nlinarith
  · have hGsq : G ≤ (G + 1) ^ 2 := by nlinarith [sq_nonneg G]
    calc
      _ = (δ ^ 2 * G) / (G + 1) ^ 2 := by rw [div_pow]; ring
      _ ≤ δ ^ 2 := (div_le_iff₀ (sq_pos_of_pos (by positivity : 0 < G + 1))).mpr
        (mul_le_mul_of_nonneg_left hGsq (sq_nonneg δ))

theorem initial_excess_horizon_of_support_tube {d : ℕ} (n : ℕ) (G : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth n G μ)
    (a : Ambient d) (r α δ b : ℝ) (hr : 0 < r) (hα : 0 ≤ α) (hδ : 0 ≤ δ) (hb : 1 ≤ b)
    (hsmall : G * α ^ 2 ≤ δ ^ 2) (K : ℕ)
    (S : AffineSubspace ℝ (Ambient d)) (hS : IsAffineNPlane n S)
    (htube : ∀ x ∈ ball a (r * (2 : ℝ) ^ K), x ∈ μ.support →
      infDist x (S : Set (Ambient d)) ≤ α * r) :
    ∀ l ≤ K, squaredExcess n μ a (r * (2 : ℝ) ^ l) ≤ (δ * b ^ l) ^ 2 := by
  intro l hl
  have hsub : ball a (r * (2 : ℝ) ^ l) ⊆ ball a (r * (2 : ℝ) ^ K) :=
    ball_subset_ball (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hl) hr.le)
  have ht := squaredExcess_le_of_support_tube n G μ hg a (r * (2 : ℝ) ^ l) (α * r)
    (by positivity) (mul_nonneg hα hr.le) S hS (fun x hx hxs => htube x (hsub hx) hxs)
  have hratio : α * r / (r * (2 : ℝ) ^ l) ≤ α := by
    apply (div_le_iff₀ (by positivity : 0 < r * (2 : ℝ) ^ l)).mpr
    have hp : 1 ≤ (2 : ℝ) ^ l := one_le_pow₀ (by norm_num)
    nlinarith [mul_nonneg (mul_nonneg hα hr.le) (sub_nonneg.mpr hp)]
  have hweight : δ ≤ δ * b ^ l := le_mul_of_one_le_right hδ (one_le_pow₀ hb)
  calc
    _ ≤ G * (α * r / (r * (2 : ℝ) ^ l)) ^ 2 := ht
    _ ≤ G * α ^ 2 := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) hratio 2) hg.1
    _ ≤ δ ^ 2 := hsmall
    _ ≤ _ := pow_le_pow_left₀ hδ hweight 2

end

end RieszRectifiability

end OAI
