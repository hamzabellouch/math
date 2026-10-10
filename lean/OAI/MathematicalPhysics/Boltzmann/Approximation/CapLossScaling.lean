import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace OAI

/-! # Cancellation of the inverse-time loss under cap dilation -/

namespace BoltzmannNonuniqueness.Cap

theorem scaled_loss_product_bound {r l a A t E H C P z ν : ℝ}
    (hr : 0 < r) (hr₁ : r ≤ 1) (hl : l ∈ Set.Icc (0:ℝ) 1)
    (ha : 0 < a) (hat : a ≤ t) (htA : t ≤ A)
    (hE : 0 ≤ E) (hH : 0 ≤ H) (hC : 0 ≤ C) (hP : 0 ≤ P)
    (hz : 0 ≤ z) (hzcap : z ≤ r*t+r*l)
    (hν : ν ≤ P*((r*t+r*l+E)*H+C/(r*t))) :
    ν*z ≤ P*(((A+1+E)*H)*(A+1)+C*(1+1/a)) := by
  have ht : 0 < t := ha.trans_le hat
  have hA : 0 ≤ A := ht.le.trans htA
  have hrt : 0 < r*t := mul_pos hr ht
  have hd : 0 ≤ r*t+r*l := add_nonneg hrt.le (mul_nonneg hr.le hl.1)
  have hdA : r*t+r*l ≤ A+1 := by
    calc
      _ = r*(t+l) := by ring
      _ ≤ r*(A+1) := mul_le_mul_of_nonneg_left (add_le_add htA hl.2) hr.le
      _ ≤ 1*(A+1) := mul_le_mul_of_nonneg_right hr₁ (by linarith)
      _ = _ := one_mul _
  have hratio : (r*t+r*l)/(r*t) ≤ 1+1/a := by
    have he : (r*t+r*l)/(r*t) = 1+l/t := by field_simp
    rw [he]
    exact add_le_add le_rfl ((div_le_div_of_nonneg_right hl.2 ht.le).trans
      (one_div_le_one_div_of_le ha hat))
  have hbase : 0 ≤ (r*t+r*l+E)*H+C/(r*t) :=
    add_nonneg (mul_nonneg (add_nonneg hd hE) hH) (div_nonneg hC hrt.le)
  calc
    ν*z ≤ (P*((r*t+r*l+E)*H+C/(r*t)))*z := mul_le_mul_of_nonneg_right hν hz
    _ ≤ (P*((r*t+r*l+E)*H+C/(r*t)))*(r*t+r*l) :=
      mul_le_mul_of_nonneg_left hzcap (mul_nonneg hP hbase)
    _ = P*(((r*t+r*l+E)*H)*(r*t+r*l)+C*((r*t+r*l)/(r*t))) := by ring
    _ ≤ P*(((A+1+E)*H)*(A+1)+C*(1+1/a)) := by
      apply mul_le_mul_of_nonneg_left _ hP
      apply add_le_add
      · exact mul_le_mul (mul_le_mul_of_nonneg_right (add_le_add hdA le_rfl) hH) hdA hd
          (mul_nonneg (by linarith) hH)
      · exact mul_le_mul_of_nonneg_left hratio hC

end BoltzmannNonuniqueness.Cap

end OAI
