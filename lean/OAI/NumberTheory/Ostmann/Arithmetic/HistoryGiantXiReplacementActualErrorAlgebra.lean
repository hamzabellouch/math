import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

namespace Ostmann.Arithmetic.HistoryGiantXiReplacementActual

theorem replacement_error_algebra (del D A η mass N S F J Q ε B r : ℝ)
    (_hD : 0 ≤ D) (_hA : 0 ≤ A) (hη : 0 ≤ η) (hm : 0 ≤ mass)
    (hN : 0 ≤ N) (hS : 0 ≤ S) (hF : 0 ≤ F) (hJ : 0 ≤ J) (_hQ : 0 ≤ Q)
    (hε : 0 ≤ ε) (hB : 0 ≤ B) (hη1 : η ≤ 1)
    (hDF : D ≤ F) (hAF : A ≤ F) (hNJ : N ≤ J) (hSQ : S ≤ Q)
    (hdel : del ≤ r) (hvar : η*Q*F*mass ≤ r) (hgrid : J*Q*F*ε ≤ r) :
    del + (2*(2*D*η)*mass + (2*D*η+A)*(N*(B*ε)))*S ≤ (5+3*B)*r := by
  have hv : (2*(2*D*η)*mass)*S ≤ 4*r := by
    calc
      _ = 4*(D*η*mass*S) := by ring
      _ ≤ 4*(F*η*mass*Q) := by gcongr
      _ = 4*(η*Q*F*mass) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hvar (by norm_num)
  have hc : 2*D*η+A ≤ 3*F := by
    have hh := mul_le_mul hDF hη1 hη hF
    nlinarith
  have he : ((2*D*η+A)*(N*(B*ε)))*S ≤ (3*B)*r := by
    calc
      _ ≤ ((3*F)*(J*(B*ε)))*Q := by gcongr
      _ = (3*B)*(J*Q*F*ε) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hgrid (by positivity)
  rw [add_mul]
  nlinarith only [hdel,hv,he]

end Ostmann.Arithmetic.HistoryGiantXiReplacementActual

end OAI
