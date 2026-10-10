import OAI.GroupTheory.PolycyclicRecognition.Analysis.CoarsePathWords
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SupportTemplates

namespace OAI

/-! # Height control survives coarse-path subdivision -/

noncomputable section

namespace PolycyclicRecognition

open Metric Set
open scoped Pointwise

variable {G W : Type*} [Group G] [MetricSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Every prefix of the short word remains close in height to the original
coarse path, with exactly the metric subdivision error. -/
theorem exists_height_controlled_word_of_coarse_path
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    (π : G →* Multiplicative W) {K : ℝ} (hK : 0 ≤ K)
    (hπ : ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ K * dist x y)
    {g : G} (γ : Path (1 : G) g) {L κ : ℝ} (hL : 0 ≤ L) (hκ : 0 ≤ κ)
    (hγ : PathMetricBound γ L κ) (E : Set W) (r B : ℝ)
    (hheight : ∀ t, ∃ z ∈ E, ‖(π (γ t)).toAdd - r • z‖ ≤ B) :
    ∃ w : List G, (∀ x ∈ w, x ∈ closedBall (1 : G) 1) ∧ w.prod = g ∧
      (w.length : ℝ) ≤ (L + 1) * (κ + 2) ∧
      ∀ j : ℕ, ∃ z ∈ E,
        ‖(π (w.take j).prod).toAdd - r • z‖ ≤ K * (κ + 2) + B := by
  obtain ⟨w, hw, hp, hlen, hnear⟩ := exists_word_near_coarse_path hpath γ hL hκ hγ
  refine ⟨w, hw, hp, hlen, ?_⟩
  intro j
  obtain ⟨t, ht⟩ := hnear j
  obtain ⟨z, hz, hh⟩ := hheight t
  refine ⟨z, hz, ?_⟩
  calc
    _ ≤ ‖(π (w.take j).prod).toAdd - (π (γ t)).toAdd‖ +
        ‖(π (γ t)).toAdd - r • z‖ := by
      simpa only [dist_eq_norm] using dist_triangle
        (π (w.take j).prod).toAdd (π (γ t)).toAdd (r • z)
    _ ≤ K * dist (w.take j).prod (γ t) + B := add_le_add (hπ _ _) hh
    _ ≤ K * (κ + 2) + B := add_le_add (mul_le_mul_of_nonneg_left ht hK) le_rfl

omit [Group G] [MetricSpace G] [IsIsometricSMul G G] in
/-- An error at scale `r` is absorbed into a fixed compact thickening of
the height template. -/
theorem exists_scaled_thickening_of_norm_sub_smul_le
    {E : Set W} {z y : W} (hz : z ∈ E) {r ε : ℝ} (hr : 0 < r)
    (h : ‖y - r • z‖ ≤ r * ε) :
    ∃ v ∈ E + closedBall (0 : W) ε, y = r • v := by
  let u := r⁻¹ • (y - r • z)
  have hu : ‖u‖ ≤ ε := by
    dsimp only [u]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
    calc
      r⁻¹ * ‖y - r • z‖ ≤ r⁻¹ * (r * ε) := mul_le_mul_of_nonneg_left h (inv_pos.mpr hr).le
      _ = ε := by rw [← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]
  refine ⟨z + u, Set.add_mem_add hz (by simpa only [mem_closedBall, dist_zero_right] using hu), ?_⟩
  dsimp only [u]
  rw [smul_add, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  abel

end PolycyclicRecognition

end

end OAI
