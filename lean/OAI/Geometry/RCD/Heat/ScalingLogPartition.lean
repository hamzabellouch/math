import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace OAI

/-! # The exact log partition of a normalized positive kernel row -/

open MeasureTheory Filter
noncomputable section
namespace RegularPointCoordinates
variable {Y : Type*} [MeasurableSpace Y] (ν : Measure Y)

theorem scaling_log_partition (K G : Y → ℝ) (y₀ : Y) {A ε : ℝ}
    (hA : 0 < A) (hε : 0 < ε) (hK : ∀ y, 0 < K y) (hG : ∀ y, 0 < G y)
    (hrow : A*(∫ y, K y*G y ∂ν)=1) :
    ε*Real.log (∫ y, Real.exp ((ε*Real.log (K y)+
      ε*(Real.log (G y)-Real.log (G y₀)))/ε) ∂ν) =
      -ε*(Real.log A+Real.log (G y₀)) := by
  have he (y : Y) : Real.exp ((ε*Real.log (K y)+
      ε*(Real.log (G y)-Real.log (G y₀)))/ε) = (K y*G y)/G y₀ := by
    have hh : (ε*Real.log (K y)+ε*(Real.log (G y)-Real.log (G y₀)))/ε =
        Real.log (K y)+Real.log (G y)-Real.log (G y₀) := by field_simp; ring
    rw [hh,Real.exp_sub,Real.exp_add,Real.exp_log (hK y),Real.exp_log (hG y),
      Real.exp_log (hG y₀)]
  have hI : 0 < ∫ y, K y*G y ∂ν :=
    pos_of_mul_pos_left (by rw [mul_comm _ A,hrow]; norm_num) hA.le
  have hh := congrArg Real.log hrow
  rw [Real.log_mul hA.ne' hI.ne',Real.log_one] at hh
  simp only [he,integral_div,Real.log_div hI.ne' (hG y₀).ne']
  nlinarith

end RegularPointCoordinates

end

end OAI
