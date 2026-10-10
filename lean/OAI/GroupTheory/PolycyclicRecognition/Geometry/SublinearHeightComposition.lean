import OAI.GroupTheory.PolycyclicRecognition.Analysis.SublinearRayIdentification

namespace OAI

/-! # Composing the linear coefficients of sublinear height maps -/

noncomputable section
namespace PolycyclicRecognition

/-- Uniform two-point sublinear errors compose. The coarse additive metric
constant contributes only to the new additive height constant. -/
theorem two_point_sublinear_height_comp
    {X W : Type*} [PseudoMetricSpace X] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (height : X → W) (f g : X → X) (A B : W →L[ℝ] W)
    {L C : ℝ} (hL : 0 ≤ L) (hC : 0 ≤ C)
    (hfLip : ∀ x y, dist (f x) (f y) ≤ L * dist x y + C)
    (hf : ∀ ε : ℝ, 0 < ε → ∃ D : ℝ, 0 ≤ D ∧ ∀ x y,
      ‖height (f y) - height (f x) - A (height y - height x)‖ ≤ ε * dist x y + D)
    (hg : ∀ ε : ℝ, 0 < ε → ∃ D : ℝ, 0 ≤ D ∧ ∀ x y,
      ‖height (g y) - height (g x) - B (height y - height x)‖ ≤ ε * dist x y + D) :
    ∀ ε : ℝ, 0 < ε → ∃ D : ℝ, 0 ≤ D ∧ ∀ x y,
      ‖height (g (f y)) - height (g (f x)) - (B.comp A) (height y - height x)‖ ≤
        ε * dist x y + D := by
  intro ε hε
  let δ := ε / (2 * (L + ‖B‖ + 1))
  have hden : 0 < 2 * (L + ‖B‖ + 1) := by positivity
  have hδ : 0 < δ := div_pos hε hden
  have heq : δ * (2 * (L + ‖B‖ + 1)) = ε := div_mul_cancel₀ ε hden.ne'
  obtain ⟨Df, hDf, hfb⟩ := hf δ hδ
  obtain ⟨Dg, hDg, hgb⟩ := hg δ hδ
  refine ⟨δ * C + Dg + ‖B‖ * Df, by positivity, ?_⟩
  intro x y
  have he : height (g (f y)) - height (g (f x)) - (B.comp A) (height y - height x) =
      (height (g (f y)) - height (g (f x)) - B (height (f y) - height (f x))) +
        B (height (f y) - height (f x) - A (height y - height x)) := by
    simp only [ContinuousLinearMap.comp_apply, map_sub]
    abel
  have hslope : δ * (L + ‖B‖) ≤ ε := by nlinarith [norm_nonneg B]
  rw [he]
  calc
    _ ≤ ‖height (g (f y)) - height (g (f x)) - B (height (f y) - height (f x))‖ +
        ‖B (height (f y) - height (f x) - A (height y - height x))‖ := norm_add_le _ _
    _ ≤ (δ * dist (f x) (f y) + Dg) + ‖B‖ * (δ * dist x y + Df) :=
      add_le_add (hgb (f x) (f y))
        ((B.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hfb x y) (norm_nonneg B)))
    _ ≤ (δ * (L * dist x y + C) + Dg) + ‖B‖ * (δ * dist x y + Df) := by
      gcongr
      exact hfLip x y
    _ ≤ ε * dist x y + (δ * C + Dg + ‖B‖ * Df) := by
      nlinarith [mul_le_mul_of_nonneg_right hslope (dist_nonneg (x := x) (y := y))]

/-- A map a bounded distance from the identity cannot have a different
linear height coefficient modulo a sublinear two-point error. -/
theorem sublinear_linear_height_error_of_close_to_id
    {X W : Type*} [PseudoMetricSpace X] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (height : X → W) (f : X → X) (A : W →L[ℝ] W)
    {K C : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hheight : ∀ x y, ‖height x - height y‖ ≤ K * dist x y)
    (hclose : ∀ x, dist (f x) x ≤ C)
    (hf : ∀ ε : ℝ, 0 < ε → ∃ D : ℝ, 0 ≤ D ∧ ∀ x y,
      ‖height (f y) - height (f x) - A (height y - height x)‖ ≤ ε * dist x y + D) :
    ∀ ε : ℝ, 0 < ε → ∃ D : ℝ, 0 ≤ D ∧ ∀ x y,
      ‖(height y - height x) - A (height y - height x)‖ ≤ ε * dist x y + D := by
  intro ε hε
  obtain ⟨D, hD, hb⟩ := hf ε hε
  refine ⟨D + 2 * K * C, by positivity, ?_⟩
  intro x y
  have hy : ‖height y - height (f y)‖ ≤ K * C := by
    rw [norm_sub_rev]
    exact (hheight (f y) y).trans (mul_le_mul_of_nonneg_left (hclose y) hK)
  have hx := (hheight (f x) x).trans (mul_le_mul_of_nonneg_left (hclose x) hK)
  have he : (height y - height x) - A (height y - height x) =
      (height y - height (f y)) +
      (height (f y) - height (f x) - A (height y - height x)) +
      (height (f x) - height x) := by abel
  rw [he]
  have hn := (norm_add_le (height y - height (f y) +
    (height (f y) - height (f x) - A (height y - height x)))
    (height (f x) - height x)).trans
    (add_le_add (norm_add_le _ _) le_rfl)
  exact hn.trans (by linarith [hb x y])

/-- Actual linearly growing height rays identify a linear map whose height
error is sublinear. This is used for the two coarse-inverse coefficients. -/
theorem linear_height_coefficient_eq_id
    {X W : Type*} [PseudoMetricSpace X] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (base : X) (height : X → W) (A : W →L[ℝ] W) (ray : W → ℝ → X)
    (hray : ∀ w t, height (ray w t) - height base = t • w)
    (hmetric : ∀ w, ∃ L C : ℝ, 0 ≤ L ∧ ∀ t : ℝ, 0 ≤ t → dist base (ray w t) ≤ L * t + C)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ D : ℝ, ∀ x,
      ‖(height x - height base) - A (height x - height base)‖ ≤ ε * dist base x + D) :
    A = ContinuousLinearMap.id ℝ W := by
  ext w
  have hz : ‖w - A w‖ = 0 := by
    by_contra hn
    have hp : 0 < ‖w - A w‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hn)
    obtain ⟨L, C, hL, hm⟩ := hmetric w
    obtain ⟨R, hR⟩ := sublinear_error_on_linear_ray base
      (fun x => (height x - height base) - A (height x - height base)) (ray w) hsub hL hm
      (‖w - A w‖ / 2) (half_pos hp)
    let t := max R 1
    have ht : 0 < t := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    have hh := hR t (le_max_left _ _) ht.le
    rw [hray, map_smul, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos ht] at hh
    nlinarith
  exact (sub_eq_zero.mp (norm_eq_zero.mp hz)).symm

end PolycyclicRecognition

end

end OAI
