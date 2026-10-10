import OAI.Analysis.PlanarPacking.SignBounds
import OAI.Analysis.PlanarPacking.DerivativeEnvelope

namespace OAI

namespace SharpPlanar
lemma error_zero_cap (a : Bool) {s : ℝ} (hs : 0 ≤ s) :
    |exactJet a 0 s-tableHJet a 0 s|<4/1000 := by
  apply (exact_table_error a 0 (by norm_num : (0:ℝ) ≤ 0) hs).trans_lt
  apply lt_of_le_of_lt _ perturbation_zero_cap
  exact mul_le_mul_of_nonneg_left (add_le_add (directEnvelope_le_rat 0) (by simpa using transformEnvelope_le_rat 0 0)) (by norm_num)
lemma error_one_cap (a : Bool) {s : ℝ} (hs : (1:ℝ)/2 ≤ s) :
    |exactJet a 1 s-tableHJet a 1 s|<11/1000 := by
  apply (exact_table_error a 1 (by norm_num : (0:ℝ) ≤ 1/2) hs).trans_lt
  apply lt_of_le_of_lt _ perturbation_one_cap
  exact mul_le_mul_of_nonneg_left (add_le_add (directEnvelope_le_rat 1) (transformEnvelope_le_half 1)) (by norm_num)
lemma error_two_cap (a : Bool) {s : ℝ} (hs : (1:ℝ)/2 ≤ s) :
    |exactJet a 2 s-tableHJet a 2 s|/2<11/1000 := by
  have he:=exact_table_error a 2 (by norm_num : (0:ℝ) ≤ 1/2) hs
  apply (div_le_div_of_nonneg_right he (by norm_num : (0:ℝ) ≤ 2)).trans_lt
  apply lt_of_le_of_lt _ perturbation_two_cap
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (add_le_add (directEnvelope_le_rat 2) (transformEnvelope_le_half 2)) (by norm_num)) (by norm_num)
lemma error_large_cap (a : Bool) {s : ℝ} (hs : 2 ≤ s) :
    |exactJet a 2 s-tableHJet a 2 s|/2<2/1000 := by
  have he:=exact_table_error a 2 (by norm_num : (0:ℝ) ≤ 2) hs
  apply (div_le_div_of_nonneg_right he (by norm_num : (0:ℝ) ≤ 2)).trans_lt
  apply lt_of_le_of_lt _ perturbation_large_cap
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (add_le_add (directEnvelope_le_rat 2) (transformEnvelope_le_rat 2 2)) (by norm_num)) (by norm_num)
end SharpPlanar

end OAI
