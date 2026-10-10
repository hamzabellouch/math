import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import OAI.NumberTheory.Ostmann.Arithmetic.MovingGiantArchimedean

namespace OAI

/-! # Logarithmic differentiation through the actual moving pivot -/

namespace Ostmann

/-- The cancellation cost is derived from the actual child-product and
pivot ranges. The large common logarithmic center cancels exactly. -/
theorem moving_pivot_cancellation_budget (v w HL HR d p T Δ E C : ℝ)
    (hv : |v| ≤ Real.exp E) (hw : |w| ≤ Real.exp E)
    (hHL : |HL| ≤ Real.exp (T + C)) (hHR : |HR| ≤ Real.exp (T + C))
    (hden : Real.exp (T - Δ - C) ≤ |d| * p) :
    |v * HR| + |w * HL| ≤ Real.exp (Real.log 2 + E + Δ + 2 * C) * (|d| * p) := by
  calc
    _ ≤ Real.exp E * Real.exp (T + C) + Real.exp E * Real.exp (T + C) := by
      rw [abs_mul, abs_mul]
      exact add_le_add (mul_le_mul hv hHR (abs_nonneg _) (Real.exp_pos _).le)
        (mul_le_mul hw hHL (abs_nonneg _) (Real.exp_pos _).le)
    _ = Real.exp (Real.log 2 + E + Δ + 2 * C) * Real.exp (T - Δ - C) := by
      symm
      rw [← Real.exp_add, show Real.log 2 + E + Δ + 2 * C + (T - Δ - C) =
        Real.log 2 + (E + (T + C)) by ring, Real.exp_add, Real.exp_add,
        Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hden (Real.exp_pos _).le

/-- Relative derivatives are stable through a linear pivot, with precisely
the cancellation factor supplied by the range estimate above. -/
theorem moving_pivot_relative_derivative (a b d X Y dX dY p A D : ℝ)
    (hd : d ≠ 0) (hX : 0 ≤ X) (hY : 0 ≤ Y) (hD : 0 ≤ D)
    (hDX : |dX| ≤ D * X) (hDY : |dY| ≤ D * Y)
    (hcancel : |a * Y| + |b * X| ≤ A * |d| * p) :
    |(a * dY - b * dX) / d| ≤ A * D * p := by
  have hleft : |a * dY| ≤ D * |a * Y| := by
    rw [abs_mul, abs_mul, abs_of_nonneg hY]
    calc
      _ ≤ |a| * (D * Y) := mul_le_mul_of_nonneg_left hDY (abs_nonneg _)
      _ = _ := by ring
  have hright : |b * dX| ≤ D * |b * X| := by
    rw [abs_mul, abs_mul, abs_of_nonneg hX]
    calc
      _ ≤ |b| * (D * X) := mul_le_mul_of_nonneg_left hDX (abs_nonneg _)
      _ = _ := by ring
  rw [abs_div]
  apply (div_le_iff₀ (abs_pos.mpr hd)).mpr
  calc
    _ ≤ |a * dY| + |b * dX| := by
      simpa only [sub_eq_add_neg, abs_neg] using (abs_add_le (a * dY) (-(b * dX)))
    _ ≤ D * (|a * Y| + |b * X|) := by nlinarith only [hleft, hright]
    _ ≤ D * (A * |d| * p) := mul_le_mul_of_nonneg_left hcancel hD
    _ = _ := by ring

theorem MovingSlotReversal.realPivot_hasDerivAt {σ : Type*}
    (step : MovingSlotReversal σ) (value : σ → ℕ)
    {L R : ℝ → ℝ} {x dL dR : ℝ} (hL : HasDerivAt L dL x) (hR : HasDerivAt R dR x) :
    HasDerivAt (fun z => step.realPivot value (L z) (R z))
      (step.realPivot value dL dR) x := by
  exact ((hR.const_mul ((step.leftFrequency : ℝ) *
      (MovingSlotReversal.naturalProduct value step.rightSlots : ℝ))).sub
    (hL.const_mul ((step.rightFrequency : ℝ) *
      (MovingSlotReversal.naturalProduct value step.leftSlots : ℝ)))).div_const _

/-- This is the derivative of the logarithm used by every internal smooth
cutoff. It applies to the literal moving-pivot formula. -/
theorem MovingSlotReversal.log_realPivot_derivative {σ : Type*}
    (step : MovingSlotReversal σ) (value : σ → ℕ)
    {L R : ℝ → ℝ} {x dL dR : ℝ} (hL : HasDerivAt L dL x) (hR : HasDerivAt R dR x)
    (hp : 0 < step.realPivot value (L x) (R x)) :
    HasDerivAt (fun z => Real.log (step.realPivot value (L z) (R z)))
      (step.realPivot value dL dR / step.realPivot value (L x) (R x)) x :=
  (step.realPivot_hasDerivAt value hL hR).log (ne_of_gt hp)

/-- The logarithmic derivative costs at most the cancellation factor times
the incoming logarithmic derivative bound. -/
theorem MovingSlotReversal.log_realPivot_derivative_bound {σ : Type*}
    (step : MovingSlotReversal σ) (value : σ → ℕ)
    (X Y dX dY A D : ℝ) (hs : step.rootFrequency ≠ 0)
    (hu : MovingSlotReversal.naturalProduct value step.compensationSlots ≠ 0)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (hD : 0 ≤ D)
    (hDX : |dX| ≤ D * X) (hDY : |dY| ≤ D * Y)
    (hp : 0 < step.realPivot value X Y)
    (hcancel : |(step.leftFrequency : ℝ) *
        (MovingSlotReversal.naturalProduct value step.rightSlots : ℝ) * Y| +
      |(step.rightFrequency : ℝ) *
        (MovingSlotReversal.naturalProduct value step.leftSlots : ℝ) * X| ≤
      A * |(step.rootFrequency : ℝ) *
        (MovingSlotReversal.naturalProduct value step.compensationSlots : ℝ)| *
          step.realPivot value X Y) :
    |step.realPivot value dX dY / step.realPivot value X Y| ≤ A * D := by
  have hd : (step.rootFrequency : ℝ) *
      (MovingSlotReversal.naturalProduct value step.compensationSlots : ℝ) ≠ 0 :=
    mul_ne_zero (Int.cast_ne_zero.mpr hs) (Nat.cast_ne_zero.mpr hu)
  have h := moving_pivot_relative_derivative _ _ _ X Y dX dY
    (step.realPivot value X Y) A D hd hX hY hD hDX hDY hcancel
  rw [abs_div, abs_of_pos hp]
  exact (div_le_iff₀ hp).mpr h

end Ostmann

end OAI
