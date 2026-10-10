import Mathlib
import OAI.Analysis.RieszRectifiability.Surfaces.RescaledBallCharts

namespace OAI

/-!
# Bounded normalized ball charts

Metric projection onto a nonempty complete convex set gives a nonexpansive retraction.
Composing this retraction with a rescaled ball chart bounds its range by a closed ball
while preserving every point of the original image in that ball. The normalization
halves the domain radius and multiplies the Lipschitz bound by two.
-/

namespace RieszRectifiability

noncomputable section

open Metric Set
open scoped NNReal

theorem exists_nonexpansive_retraction_of_complete_convex {d : ℕ}
    (K : Set (Ambient d)) (hne : K.Nonempty) (hcomplete : IsComplete K) (hconvex : Convex ℝ K) :
    ∃ p : Ambient d → Ambient d, LipschitzWith 1 p ∧
      (∀ x, p x ∈ K) ∧ ∀ x ∈ K, p x = x := by
  classical
  choose p hp hmin using exists_norm_eq_iInf_of_complete_convex hne hcomplete hconvex
  have hv (x : Ambient d) : ∀ w ∈ K, inner ℝ (x - p x) (w - p x) ≤ 0 :=
    (norm_eq_iInf_iff_real_inner_le_zero hconvex (hp x)).mp (hmin x)
  refine ⟨p, ?_, hp, ?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    have hx := hv x (p y) (hp y)
    have hy := hv y (p x) (hp x)
    have hid : inner ℝ (x - y) (p x - p y) = ‖p x - p y‖ ^ 2 -
        inner ℝ (x - p x) (p y - p x) - inner ℝ (y - p y) (p x - p y) := by
      rw [← real_inner_self_eq_norm_sq]
      simp only [inner_sub_left, inner_sub_right]
      ring
    have hc := real_inner_le_norm (x - y) (p x - p y)
    simp only [NNReal.coe_one, one_mul, dist_eq_norm]
    nlinarith [norm_nonneg (x - y), norm_nonneg (p x - p y)]
  · intro x hx
    have h := hv x x hx
    rw [real_inner_self_eq_norm_sq] at h
    have hz : ‖x - p x‖ = 0 := by nlinarith [norm_nonneg (x - p x)]
    exact (sub_eq_zero.mp (norm_eq_zero.mp hz)).symm

theorem exists_bounded_normalized_ball_chart {n d : ℕ}
    (r : ℝ) (c : Ambient d) (b : ℝ) (hb : 0 ≤ b)
    (f : ball (0 : Ambient n) (2 * r) → Ambient d) (M : ℝ≥0) (hf : LipschitzWith M f) :
    ∃ g : ball (0 : Ambient n) r → Ambient d,
      LipschitzWith (M * 2) g ∧ Set.range g ⊆ closedBall c b ∧
      (closedBall c b ∩ Set.range f) ⊆ Set.range g := by
  obtain ⟨p, hp, hpRange, hpFix⟩ := exists_nonexpansive_retraction_of_complete_convex
    (closedBall c b) ⟨c, mem_closedBall_self hb⟩ isClosed_closedBall.isComplete (convex_closedBall c b)
  obtain ⟨h, hhLip, hhRange⟩ := exists_rescaled_ball_chart (2 * r) (0 : Ambient n)
    2 (by norm_num) f M hf
  have heq : (2 * r) / ((2 : ℝ≥0) : ℝ) = r := by change (2 * r) / 2 = r; ring
  rw [heq] at hhLip hhRange
  let h' : ball (0 : Ambient n) r → Ambient d := (ball (0 : Ambient n) r).domRestrict h
  have hh'Lip : LipschitzWith (M * 2) h' := hhLip.to_restrict
  have hh'Range : Set.range h' = Set.range f := by
    apply Set.Subset.antisymm
    · rintro y ⟨u, rfl⟩
      exact hhRange ▸ mem_image_of_mem h u.property
    · intro y hy
      obtain ⟨u, hu, he⟩ := hhRange ▸ hy
      exact ⟨⟨u, hu⟩, he⟩
  refine ⟨p ∘ h', ?_, ?_, ?_⟩
  · simpa only [one_mul] using! hp.comp hh'Lip
  · rintro y ⟨u, rfl⟩
    exact hpRange (h' u)
  · intro y hy
    obtain ⟨u, hu⟩ := hh'Range ▸ hy.2
    exact ⟨u, by change p (h' u) = y; rw [hu, hpFix y hy.1]⟩

end

end RieszRectifiability

end OAI
