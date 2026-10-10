import Mathlib

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337

/-- The standard character is the circle exponential of a normalized residue. -/
theorem stdAddChar_of_val_div {q : ℕ} [NeZero q] (y : ZMod q) (x : ℝ)
    (hx : (y.val : ℝ) / q = x) :
    ZMod.stdAddChar y = (Circle.exp (2 * Real.pi * x) : ℂ) := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_eq_circleExp, hx]

/-- Frequency multiplication becomes the ordinary natural power of the phase. -/
theorem stdAddChar_frequency_of_val_div {q : ℕ} [NeZero q]
    (y : ZMod q) (x : ℝ) (hx : (y.val : ℝ) / q = x) (l : ℕ) :
    ZMod.stdAddChar ((l : ZMod q) * y) = (Circle.exp (2 * Real.pi * x) : ℂ) ^ l := by
  rw [← nsmul_eq_mul, AddChar.map_nsmul_eq_pow, stdAddChar_of_val_div y x hx]

/-- Equivalent exponential form of the frequency identity. -/
theorem stdAddChar_frequency_exp_of_val_div {q : ℕ} [NeZero q]
    (y : ZMod q) (x : ℝ) (hx : (y.val : ℝ) / q = x) (l : ℕ) :
    ZMod.stdAddChar ((l : ZMod q) * y) =
      (Circle.exp (2 * Real.pi * (l : ℝ) * x) : ℂ) := by
  rw [stdAddChar_frequency_of_val_div y x hx, Circle.coe_exp, Circle.coe_exp,
    ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- Fourier sums transfer without any loss, also for repeated indexed samples. -/
theorem stdAddChar_sum_of_val_div {ι : Type*} {q : ℕ} [NeZero q]
    (s : Finset ι) (y : ι → ZMod q) (x : ι → ℝ)
    (hx : ∀ i ∈ s, ((y i).val : ℝ) / q = x i) (l : ℕ) :
    (∑ i ∈ s, ZMod.stdAddChar ((l : ZMod q) * y i)) =
      ∑ i ∈ s, (Circle.exp (2 * Real.pi * x i) : ℂ) ^ l := by
  exact Finset.sum_congr rfl (fun i hi => stdAddChar_frequency_of_val_div (y i) (x i) (hx i hi) l)

/-- Rational common-denominator identities specialize the real-valued phase identity. -/
theorem stdAddChar_frequency_of_rational_val_div {q : ℕ} [NeZero q]
    (y : ZMod q) (x : ℚ) (hx : (y.val : ℚ) / q = x) (l : ℕ) :
    ZMod.stdAddChar ((l : ZMod q) * y) =
      (Circle.exp (2 * Real.pi * (x : ℝ)) : ℂ) ^ l := by
  apply stdAddChar_frequency_of_val_div
  simpa only [Rat.cast_div, Rat.cast_natCast] using congrArg (fun z : ℚ => (z : ℝ)) hx

end Problem337

end

end OAI
