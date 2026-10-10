import OAI.Geometry.RCD.Sobolev.LipschitzMetricTransfer

namespace OAI

/-! # Transfer on the actual pointed approximation maps -/

open Set Metric
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X]

theorem pointed_function_transfer {n : ℕ} {p : X} {r S ε T A : ℝ}
    (hr : 0<r) (hS : 0≤S) (hε : 0≤ε) (hε1 : ε≤1)
    {v : X → Euclidean n} (hv : IsPointedApproximation p 0 r S ε v)
    (u : X → ℝ) (L : ℝ≥0)
    (hu : ∀ x, dist x p ≤ S*r → |u x| ≤ A)
    (hl : ∀ x z, dist x p ≤ S*r → dist z p ≤ S*r →
      |u x-u z| ≤ (L:ℝ)*(dist x z/r)) :
    ∃ g : Euclidean n → ℝ, LipschitzWith L g ∧
      (∀ x, dist x p ≤ S*r → |g (v x)-u x| ≤ L*ε) ∧
      (∀ y, ‖y‖ ≤ T → |g y| ≤ A+L*(T+2)) := by
  let s := closedBall p (S*r)
  have hp : p ∈ s := mem_closedBall_self (mul_nonneg hS hr.le)
  have hApprox : ∀ x ∈ s, ∀ z ∈ s, |u x-u z| ≤ L*dist (v x) (v z)+L*ε := by
    intro x hx z hz
    have hd := (abs_le.mp (hv.2.1 x z hx hz)).1
    have hm := mul_le_mul_of_nonneg_left (show dist x z/r ≤ dist (v x) (v z)+ε by linarith) L.coe_nonneg
    exact (hl x z hx hz).trans (by nlinarith only [hm])
  obtain ⟨g,hg,hgu⟩ := exists_lipschitz_metric_transfer ⟨p,hp⟩ u v L
    (mul_nonneg L.coe_nonneg hε) (fun x hx => (neg_le_neg (hu x hx)).trans (neg_abs_le (u x)))
    hApprox
  refine ⟨g,hg,hgu,?_⟩
  intro y hy
  have hgp : |g (v p)| ≤ A+L := by
    have ht := abs_add_le (g (v p)-u p) (u p)
    have hb := hgu p hp
    have hc := mul_le_mul_of_nonneg_left hε1 L.coe_nonneg
    have hpA := hu p hp
    simp only [sub_add_cancel] at ht
    linarith
  have hd : dist y (v p) ≤ T+1 := by
    have hvp : ‖v p‖ ≤ ε := by simpa only [dist_zero_right] using hv.1
    calc dist y (v p) ≤ dist y 0+dist 0 (v p) := dist_triangle _ _ _
      _ ≤ T+1 := by simpa only [dist_zero_right,dist_zero_left] using add_le_add hy (hvp.trans hε1)
  have hgd : |g y-g (v p)| ≤ L*dist y (v p) := by
    simpa only [Real.dist_eq] using hg.dist_le_mul y (v p)
  have hgdist : |g y-g (v p)| ≤ L*(T+1) :=
    hgd.trans (mul_le_mul_of_nonneg_left hd L.coe_nonneg)
  have ht := abs_add_le (g y-g (v p)) (g (v p))
  simp only [sub_add_cancel] at ht
  nlinarith only [ht,hgdist,hgp]

end RegularPointCoordinates

end

end OAI
