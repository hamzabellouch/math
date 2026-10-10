import OAI.Geometry.CylinderCovering.Cubic.Similarity

namespace OAI

noncomputable section
open TriangularCovering

namespace CylinderCovering.Cubic

lemma profile_eq_eight_d (q : ℝ) : profile q = 8 * TriangularCovering.d q := by
  unfold profile TriangularCovering.d
  ring

lemma profileMax_eq_eight_max_d (a b : ℝ) :
    profileMax a b = 8 * max (TriangularCovering.d a) (TriangularCovering.d b) := by
  unfold profileMax
  rw [profile_eq_eight_d, profile_eq_eight_d, mul_max_of_nonneg]
  norm_num

lemma rescaled_cap (τ a b : ℝ) :
    cap (τ / 2) a b / 2 = 1 / 2 + τ ^ 2 *
      (max (TriangularCovering.d a) (TriangularCovering.d b) + 25 / 4 * τ) := by
  unfold cap
  rw [profileMax_eq_eight_max_d]
  ring

lemma rescaled_count (τ : ℝ) : n (τ / 2) = ⌈8 / τ ^ 2⌉₊ := by
  unfold n
  congr 1
  ring

lemma rescaled_alpha (τ a b : ℝ) :
    τ / 2 * alpha a b = τ * TriangularCovering.alpha a b := by
  unfold alpha TriangularCovering.alpha
  ring

lemma rescaled_beta (τ a b : ℝ) :
    τ / 2 * beta a b = τ * TriangularCovering.beta a b := by
  unfold beta TriangularCovering.beta
  ring

lemma rescaled_cost_main_term (τ : ℝ) :
    (2 * H - H / 15 * (τ / 2) ^ 2) / (4 * H) =
      1 / 2 - 1 / 240 * τ ^ 2 := by
  field_simp [H_ne_zero]
  ring

lemma rescaled_remainder {S C τ : ℝ}
    (h : |S - (2 * H - H / 15 * (τ / 2) ^ 2)| ≤ C * (τ / 2) ^ 3) :
    |S / (4 * H) - (1 / 2 - 1 / 240 * τ ^ 2)| ≤
      C / (32 * H) * τ ^ 3 := by
  have hH : 0 < 4 * H := mul_pos (by norm_num) H_pos
  have heq : S / (4 * H) - (1 / 2 - 1 / 240 * τ ^ 2) =
      (S - (2 * H - H / 15 * (τ / 2) ^ 2)) / (4 * H) := by
    rw [sub_div, rescaled_cost_main_term]
  rw [heq, abs_div, abs_of_pos hH]
  have hh := div_le_div_of_nonneg_right h hH.le
  calc
    _ ≤ (C * (τ / 2) ^ 3) / (4 * H) := hh
    _ = C / (32 * H) * τ ^ 3 := by ring

end CylinderCovering.Cubic

end

end OAI
