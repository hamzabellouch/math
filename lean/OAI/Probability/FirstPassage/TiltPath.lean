import OAI.Probability.FirstPassage.Paths
import Mathlib.Tactic.FieldSimp

namespace OAI

namespace PlanarFPP

theorem pathCost_scale (τ : Edge → ℝ) (α : ℝ) (p : Vertex) (ds : List Step) :
    pathCost (fun e => α * τ e) p ds = α * pathCost τ p ds := by
  induction ds generalizing p with
  | nil => simp [pathCost]
  | cons d ds ih => simp [pathCost, ih, mul_add]

theorem tilt_crossing_defect (τ : Edge → ℝ) (b m a K lam s n : ℝ)
    (hK : 0 ≤ K) (hlam : 0 ≤ lam) (hs : 0 < s) (hn : 0 < n)
    (hsmall : lam * s < n) (hgain : K + 16 * |a| + 1 < lam * m)
    (p : Vertex) (ds : List Step)
    (hx : ((displacement ds).1 : ℝ) = n)
    (hr : |transverse b (displacement ds)| ≤ 16 * s)
    (hcheap : pathCost τ p ds < m * n + K * s) :
    defect (fun e => (1 - lam * s / n) * τ e) b m a p ds < -s := by
  have hα : 0 < 1 - lam * s / n := by
    have := (div_lt_one hn).mpr hsmall
    linarith
  have hc := mul_lt_mul_of_pos_left hcheap hα
  have habs : -(a * transverse b (displacement ds)) ≤ 16 * |a| * s := by
    calc
      -(a * transverse b (displacement ds)) ≤ |a * transverse b (displacement ds)| :=
        neg_le_abs _
      _ = |a| * |transverse b (displacement ds)| := abs_mul _ _
      _ ≤ |a| * (16 * s) := mul_le_mul_of_nonneg_left hr (abs_nonneg a)
      _ = 16 * |a| * s := by ring
  have halg : (1 - lam * s / n) * (m * n + K * s) - m * n =
      (K - lam * m) * s - lam * K * s ^ 2 / n := by
    field_simp [ne_of_gt hn]
    ring
  have hnonneg : 0 ≤ lam * K * s ^ 2 / n := by positivity
  have hgain' := mul_lt_mul_of_pos_right hgain hs
  unfold defect support
  rw [pathCost_scale, hx]
  nlinarith

end PlanarFPP

end OAI
