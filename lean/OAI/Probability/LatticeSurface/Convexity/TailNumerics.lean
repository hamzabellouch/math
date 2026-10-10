import Mathlib

namespace OAI

example : (8:ENNReal)^2*(1/1024) = 1/16 := by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num

example : (4:ENNReal)*(1/16) = 1/4 := by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num

example : (25:ENNReal)*(1-(1/4:ENNReal))⁻¹ ≤ 100 := by
  have hn : (1-(1/4:ENNReal)) ≠ 0 := by
    rw [ne_eq,tsub_eq_zero_iff_le]
    norm_num [ENNReal.le_inv_iff_mul_le]
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_mul,ENNReal.toReal_inv,ENNReal.toReal_sub_of_le (by norm_num : (1/4:ENNReal)≤1)]

end OAI
