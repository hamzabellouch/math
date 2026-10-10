import Mathlib
import OAI.Geometry.Cannon.Flows.State

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
section
namespace CannonMagnification

open Set Metric

lemma annular_pattern_distance {X : Type*} [MetricSpace X]
    (h : X ≃ₜ X) (x y z : X) (R θ C L a d P : ℝ)
    (hR : 0 < R) (hθ : 0 ≤ θ) (ha : 0 < a) (hC : 0 ≤ C)
    (hexp : Expansion h x R C L)
    (hy : a*R ≤ dist x y) (hz : a*R ≤ dist x z)
    (hyz : dist y z ≤ d*θ*R) (hcoef : C*d ≤ P*a^2) :
    dist (h y) (h z) ≤ P*θ := by
  have hprod : a^2*R^2 ≤ max R (dist x y)*max R (dist x z) := by
    calc
      _ = (a*R)*(a*R) := by ring
      _ ≤ _ := mul_le_mul (hy.trans (le_max_right _ _)) (hz.trans (le_max_right _ _))
        (mul_nonneg ha.le hR.le) (hR.le.trans (le_max_left _ _))
  have hh := (mul_le_mul_of_nonneg_left hprod (dist_nonneg (x := h y) (y := h z))).trans
    (by simpa only [mul_assoc] using (hexp y z).1)
  have hCdist := mul_le_mul_of_nonneg_left hyz (mul_nonneg hC hR.le)
  have hcoeff := mul_le_mul_of_nonneg_right hcoef (mul_nonneg hθ (sq_nonneg R))
  apply (mul_le_mul_iff_left₀ (mul_pos (sq_pos_of_pos ha) (sq_pos_of_pos hR))).mp
  nlinarith only [hh,hCdist,hcoeff]

lemma inverse_ball_criterion {X : Type*} [MetricSpace X]
    (h : X ≃ₜ X) (x y z : X) (R C L d s : ℝ)
    (hR : 0 < R) (hL : 0 ≤ L) (hd : 0 < d) (hs : 0 ≤ s)
    (hexp : Expansion h x R C L)
    (hcoef : L*s*denominator x R y*(denominator x R y+d) < R*d)
    (hyz : dist (h y) (h z) ≤ s) : dist y z < d := by
  by_contra hh
  have hdd : d ≤ dist y z := le_of_not_gt hh
  have hD : 0 < denominator x R y := hR.trans_le (le_max_left _ _)
  have hDz : 0 ≤ denominator x R z := hR.le.trans (le_max_left _ _)
  have htri := denominator_triangle x y z R
  have hscale : denominator x R z*d ≤ (denominator x R y+d)*dist y z := by
    have hh := mul_le_mul_of_nonneg_right htri hd.le
    have hh' := mul_le_mul_of_nonneg_left hdd hD.le
    nlinarith only [hh,hh']
  have he := (hexp y z).2
  change R*dist y z ≤ L*dist (h y) (h z)*denominator x R y*denominator x R z at he
  have he' := mul_le_mul_of_nonneg_right he hd.le
  have hu := mul_le_mul_of_nonneg_left hyz hL
  have hu' := mul_le_mul_of_nonneg_right hu (mul_nonneg hD.le (mul_nonneg hDz hd.le))
  have hv := mul_le_mul_of_nonneg_left hscale (mul_nonneg (mul_nonneg hL hs) hD.le)
  have hc := mul_lt_mul_of_pos_right hcoef (hd.trans_le hdd)
  nlinarith only [he',hu',hv,hc]

lemma pattern_ball_containment {X : Type*} [MetricSpace X]
    (h : X ≃ₜ X) (x y : X) (R θ C L B c p : ℝ)
    (hR : 0 < R) (hθ : 0 < θ) (hL : 0 ≤ L) (hB : 1 ≤ B)
    (hc : 0 < c) (hp : 0 ≤ p) (hsmall : c*θ ≤ 1)
    (hexp : Expansion h x R C L) (hy : dist x y ≤ B*R)
    (hcoef : L*p*B*(B+1) < c) :
    closedBall (h y) (p*θ) ⊆ h '' ball y (c*θ*R) := by
  intro z hz
  refine ⟨h.symm z,?_,h.apply_symm_apply z⟩
  have hD : denominator x R y ≤ B*R := max_le (by nlinarith only [hB,hR]) hy
  have hDnon : 0 ≤ denominator x R y := hR.le.trans (le_max_left _ _)
  have hDplus : denominator x R y+c*θ*R ≤ (B+1)*R := by
    have hm := mul_le_mul_of_nonneg_right hsmall hR.le
    linarith only [hD,hm]
  have hco : L*(p*θ)*denominator x R y*(denominator x R y+c*θ*R) < R*(c*θ*R) := by
    have hmul : L*(p*θ)*denominator x R y*(denominator x R y+c*θ*R) ≤
        L*(p*θ)*(B*R)*((B+1)*R) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hD (by positivity)
      · exact hDplus
      · positivity
      · positivity
    have hh := mul_lt_mul_of_pos_right hcoef (mul_pos hθ (sq_pos_of_pos hR))
    nlinarith only [hmul,hh]
  have hh := inverse_ball_criterion h x y (h.symm z) R C L (c*θ*R) (p*θ)
    hR hL (by positivity) (by positivity) hexp hco (by
      rw [h.apply_symm_apply,dist_comm]
      exact mem_closedBall.mp hz)
  simpa only [mem_ball,dist_comm] using hh

lemma net_pattern_ball {X : Type*} [MetricSpace X] (c z : X) (e : ℝ)
    (he : 0 ≤ e) (hcz : dist c z ≤ e) :
    closedBall c (e/2) ⊆ closedBall z (3*e) ∧
    closedBall z (3*e) ⊆ closedBall c (10*e) := by
  constructor
  · intro w hw
    have hdist := dist_triangle w c z
    have hw' := mem_closedBall.mp hw
    exact mem_closedBall.mpr (by linarith only [hdist,hw',hcz,he])
  · intro w hw
    have hdist := dist_triangle w z c
    have hw' := mem_closedBall.mp hw
    rw [dist_comm z c] at hdist
    exact mem_closedBall.mpr (by linarith only [hdist,hw',hcz,he])

end CannonMagnification

end

end
end
end
end
end
end
end
end
end

end OAI
