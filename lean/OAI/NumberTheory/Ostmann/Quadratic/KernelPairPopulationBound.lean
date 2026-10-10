import OAI.NumberTheory.Ostmann.Quadratic.KernelPopulationBound

namespace OAI

/-! # The population product estimate for a prescribed kernel product -/

namespace Ostmann

theorem root_population_product_bound (X m a b C : ℝ)
    (hX : 0 ≤ X) (hm : 0 ≤ m) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (C * (Real.sqrt (X / a) + Real.sqrt m)) *
      (C * (Real.sqrt (X / b) + Real.sqrt m)) ≤
      C ^ 2 * (X / Real.sqrt (a * b) + 2 * Real.sqrt (X * m) + m) := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hroota : Real.sqrt (X / a) ≤ Real.sqrt X :=
    Real.sqrt_le_sqrt ((div_le_self hX ha).trans le_rfl)
  have hrootb : Real.sqrt (X / b) ≤ Real.sqrt X :=
    Real.sqrt_le_sqrt (div_le_self hX hb)
  have hab : Real.sqrt (X / a) * Real.sqrt (X / b) = X / Real.sqrt (a * b) := by
    rw [Real.sqrt_div hX, Real.sqrt_div hX, div_mul_div_comm,
      Real.mul_self_sqrt hX, ← Real.sqrt_mul ha0.le]
  have hm2 := Real.sq_sqrt hm
  have hac := mul_le_mul_of_nonneg_right hroota (Real.sqrt_nonneg m)
  have hbc := mul_le_mul_of_nonneg_right hrootb (Real.sqrt_nonneg m)
  have hinside : (Real.sqrt (X / a) + Real.sqrt m) *
      (Real.sqrt (X / b) + Real.sqrt m) ≤
        X / Real.sqrt (a * b) + 2 * Real.sqrt (X * m) + m := by
    rw [Real.sqrt_mul hX]
    nlinarith
  have hh := mul_le_mul_of_nonneg_left hinside (sq_nonneg C)
  convert hh using 1
  ring

end Ostmann

end OAI
