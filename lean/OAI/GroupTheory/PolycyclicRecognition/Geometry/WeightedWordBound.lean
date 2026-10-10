import OAI.GroupTheory.PolycyclicRecognition.Geometry.WeightedWordNorm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

namespace OAI

/-! # Word-length control by a weighted norm

Short-cost factors are accumulated until they leave a small identity ball.
Each completed block has bounded word length and pays for that length.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped NNReal

variable {G : Type*} [Group G]

/-- The residual factor stays in the small ball; every flushed block is
charged against the accumulated cost. -/
theorem seminorm_product_cost_bound
    (p w : GroupSeminorm G) (c : G → ℝ≥0) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hpc : ∀ g, p g ≤ c g)
    (hlocal : ∀ g, p g ≤ δ → w g ≤ 1)
    (hwc : ∀ g, w g ≤ max 1 (c g : ℝ))
    (l : List G) :
    w l.prod ≤ (4 / δ) * (productCost c l : ℝ) + 1 := by
  let C : ℝ := 4 / δ
  have hC : 0 < C := div_pos (by norm_num) hδ
  have hCδ : C * δ = 4 := by dsimp [C]; field_simp
  have hC2 : 2 ≤ C := by nlinarith
  have hmain : ∀ (l : List G) (a : G) (r : ℝ),
      p a ≤ r → 0 ≤ r → r < δ / 2 →
      w (a * l.prod) ≤ C * (r + (productCost c l : ℝ)) + 1 := by
    intro l
    induction l with
    | nil =>
      intro a r ha hr hrδ
      simpa only [List.prod_nil, mul_one, productCost_nil, NNReal.coe_zero, add_zero] using
        (hlocal a (ha.trans (by linarith))).trans
          (by have := mul_nonneg hC.le hr; linarith)
    | cons b l ih =>
      intro a r ha hr hrδ
      have hb0 : (0 : ℝ) ≤ c b := (c b).coe_nonneg
      by_cases hsmall : r + (c b : ℝ) < δ / 2
      · have hab : p (a * b) ≤ r + (c b : ℝ) :=
          (p.mul_le' a b).trans (add_le_add ha (hpc b))
        have h := ih (a * b) (r + c b) hab (by linarith) hsmall
        simpa only [List.prod_cons, productCost_cons, NNReal.coe_add, add_assoc,
          mul_assoc] using h
      · have hpaid : w (a * b) ≤ C * (r + (c b : ℝ)) := by
          have hsum : δ / 2 ≤ r + (c b : ℝ) := le_of_not_gt hsmall
          by_cases hb : (c b : ℝ) < δ / 2
          · have hab : p (a * b) ≤ δ := by
              have hp := (p.mul_le' a b).trans (add_le_add ha (hpc b))
              change p (a * b) ≤ r + (c b : ℝ) at hp
              linarith
            have hpay : 1 ≤ C * (r + (c b : ℝ)) := by nlinarith
            exact (hlocal (a * b) hab).trans hpay
          · have hbδ : δ / 2 ≤ (c b : ℝ) := le_of_not_gt hb
            have haW : w a ≤ 1 := hlocal a (ha.trans (by linarith))
            have hbW := hwc b
            have hpay : 1 + max 1 (c b : ℝ) ≤ C * (c b : ℝ) := by
              rcases le_total (c b : ℝ) 1 with h | h
              · rw [max_eq_left h]
                nlinarith
              · rw [max_eq_right h]
                nlinarith
            exact ((w.mul_le' a b).trans (add_le_add haW hbW)).trans
              (hpay.trans (mul_le_mul_of_nonneg_left (by linarith) hC.le))
        have hrest := ih 1 0 (by simp) le_rfl (half_pos hδ)
        simp only [one_mul, zero_add] at hrest
        have hbound := (w.mul_le' (a * b) l.prod).trans (add_le_add hpaid hrest)
        change w (a * (b * l.prod)) ≤ C * (r + ((c b : ℝ) + (productCost c l : ℝ))) + 1
        rw [← mul_assoc]
        calc
          _ ≤ C * (r + (c b : ℝ)) + (C * (productCost c l : ℝ) + 1) := hbound
          _ = _ := by ring
  simpa only [one_mul, zero_add] using hmain l 1 0 (by simp) le_rfl (half_pos hδ)

end PolycyclicRecognition

end

end OAI
