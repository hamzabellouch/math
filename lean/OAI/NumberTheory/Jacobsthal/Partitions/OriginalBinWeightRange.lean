import OAI.NumberTheory.Jacobsthal.Estimates.SubbinAggregation

namespace OAI

namespace Erdos970


namespace ErdosStoppedArithmetic
open ErdosInversePrimeBin ErdosStoppedSubbinAggregation


theorem original_bin_weight_range (Y q R theta : ℝ) (hY : 0 ≤ Y) (hq : 0 < q)
    (hR : 0 < R) (ht : 0 ≤ theta) (ht1 : theta ≤ 1) :
    0 ≤ Y/(((1+theta)*R)*q) ∧ ∀ p ∈ primeBin R theta,
      Y/(((1+theta)*R)*q) ≤ Y/((p : ℝ)*q) ∧
      Y/((p : ℝ)*q) ≤ 2*(Y/(((1+theta)*R)*q)) := by
  have hDen : 0 < ((1+theta)*R)*q := by positivity
  have hDen0 : 0 < R*q := mul_pos hR hq
  have hDenBound : ((1+theta)*R)*q ≤ 2*(R*q) := by
    have hh := mul_le_mul_of_nonneg_right (show 1+theta ≤ (2 : ℝ) by linarith) hDen0.le
    nlinarith only [hh]
  refine ⟨div_nonneg hY hDen.le,?_⟩
  intro p hp
  obtain ⟨_hp,hlo,hhi⟩ := (mem_primeBin hR.le ht p).mp hp
  refine ⟨reference_length_le hY hq (hR.trans hlo) hhi,?_⟩
  calc
    Y/((p : ℝ)*q) ≤ Y/(R*q) := reference_length_le hY hq hR hlo.le
    _ ≤ (2*Y)/(((1+theta)*R)*q) := by
      apply (div_le_div_iff₀ hDen0 hDen).mpr
      have hh := mul_le_mul_of_nonneg_left hDenBound hY
      nlinarith only [hh]
    _ = _ := by ring

end ErdosStoppedArithmetic


end Erdos970

end OAI
