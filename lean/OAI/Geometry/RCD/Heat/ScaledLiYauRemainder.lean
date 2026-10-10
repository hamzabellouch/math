import Mathlib

namespace OAI

/-! # Uniform interior-time bound for the scaled Li--Yau remainder -/

namespace RegularPointCoordinates

theorem scaled_liYau_remainder_le {c δ t u N k m : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hδ : 0 < δ)
    (ht : δ ≤ t) (ht' : δ ≤ u) (hN : 0 ≤ N) (hk : 0 ≤ k)
    (hm0 : 0 ≤ m) (hm1 : m ≤ 1) :
    c^2*((N*(1+c)^2/2)*(2*k/c+1/(c*t)+1/(c*u))*m) ≤
      c*(4*N*k+4*N/δ) := by
  have ht0 := hδ.trans_le ht
  have ht1 := hδ.trans_le ht'
  have hp : (1+c)^2 ≤ 4 := by nlinarith
  have htime : 2*k+1/t+1/u ≤ 2*k+2/δ := by
    have ha := one_div_le_one_div_of_le hδ ht
    have hb := one_div_le_one_div_of_le hδ ht'
    calc
      _ = 2*k+(1/t+1/u) := by ring
      _ ≤ 2*k+(1/δ+1/δ) := add_le_add le_rfl (add_le_add ha hb)
      _ = _ := by ring
  have hcoef : N*(1+c)^2/2 ≤ 2*N := by nlinarith
  have hbase0 : 0 ≤ 2*k+1/t+1/u := by positivity
  calc
    c^2*((N*(1+c)^2/2)*(2*k/c+1/(c*t)+1/(c*u))*m) =
        (N*(1+c)^2/2)*c*(2*k+1/t+1/u)*m := by
      field_simp [hc.ne',ht0.ne',ht1.ne']
    _ ≤ (2*N)*c*(2*k+2/δ)*1 := by
      exact mul_le_mul (mul_le_mul
        (mul_le_mul_of_nonneg_right hcoef hc.le) htime hbase0 (by positivity))
        hm1 hm0 (by positivity)
    _ = c*(4*N*k+4*N/δ) := by ring

end RegularPointCoordinates

end OAI
