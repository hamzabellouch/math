import OAI.Analysis.Laughlin.FiniteFlux.Quadruples08
import OAI.Analysis.Laughlin.FourBody.FastChoose

namespace OAI

namespace Laughlin.Certificate
open scoped Matrix

theorem gram_8_1_1 : Z 8 1 1 = (0 : ℚ) := by
  rw [Z_eq_fast]
  unfold ZFast
  rw [quadruples_8]
  decide +kernel

theorem gram_8_1_3 : Z 8 1 3 = (0 : ℚ) := by
  rw [Z_eq_fast]
  unfold ZFast
  rw [quadruples_8]
  decide +kernel

theorem gram_8_1_5 : Z 8 1 5 = (0 : ℚ) := by
  rw [Z_eq_fast]
  unfold ZFast
  rw [quadruples_8]
  decide +kernel

theorem gram_8_1_7 : Z 8 1 7 = (0 : ℚ) := by
  rw [Z_eq_fast]
  unfold ZFast
  rw [quadruples_8]
  decide +kernel

theorem gram_8_3_3 : Z 8 3 3 = (720 : ℚ) := by
  rw [Z_eq_fast]
  unfold ZFast
  rw [quadruples_8]
  decide +kernel

theorem gram_8_3_5 : Z 8 3 5 = (-720 : ℚ) := by
  rw [Z_eq_fast]
  unfold ZFast
  rw [quadruples_8]
  decide +kernel

theorem gram_8_3_7 : Z 8 3 7 = (1260 : ℚ) := by
  rw [Z_eq_fast]
  unfold ZFast
  rw [quadruples_8]
  decide +kernel

theorem gram_8_5_5 : Z 8 5 5 = (720 : ℚ) := by
  rw [Z_eq_fast]
  unfold ZFast
  rw [quadruples_8]
  decide +kernel

theorem gram_8_5_7 : Z 8 5 7 = (-1260 : ℚ) := by
  rw [Z_eq_fast]
  unfold ZFast
  rw [quadruples_8]
  decide +kernel

theorem gram_8_7_7 : Z 8 7 7 = (2205 : ℚ) := by
  rw [Z_eq_fast]
  unfold ZFast
  rw [quadruples_8]
  decide +kernel

end Laughlin.Certificate

end OAI
