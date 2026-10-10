import OAI.NumberTheory.CubicMoment.Estimates.TailPrimeRange

namespace OAI

/-! The actual intermediate prime-group range meets both length and
height hypotheses of the enlarged dispersion estimate, with fixed support
widths retained. -/
noncomputable section
open Filter
namespace CubicFirstMoment

theorem eventually_tailPrime_middle_upper :
    ∀ᶠ X : ℝ in atTop, ∀ A B : ℝ, 0 < B → A*B ≤ 3*X →
      X^(39/100:ℝ) ≤ B → A ≤ B^(19/10:ℝ) := by
  filter_upwards [eventually_ge_atTop (1:ℝ),
    eventually_const_mul_rpow_le (show (1:ℝ) < 1131/1000 by norm_num) 3]
    with X hX hgap
  intro A B hB hAB hBX
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hp : 3*X ≤ B^(29/10:ℝ) := by
    calc
      _ = 3*X^(1:ℝ) := by rw [Real.rpow_one]
      _ ≤ X^(1131/1000:ℝ) := hgap
      _ = (X^(39/100:ℝ))^(29/10:ℝ) := by rw [←Real.rpow_mul hXp.le]; norm_num
      _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg hXp.le _) hBX (by norm_num)
  have he : B*B^(19/10:ℝ) = B^(29/10:ℝ) := by
    calc
      _ = B^(1:ℝ)*B^(19/10:ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [←Real.rpow_add hB]; norm_num
  apply (mul_le_mul_iff_left₀ hB).mp
  calc
    A*B ≤ 3*X := hAB
    _ ≤ B^(29/10:ℝ) := hp
    _ = B^(19/10:ℝ)*B := by rw [←he]; ring

theorem eventually_tailPrime_middle_height {C : ℝ} (hC : 0 < C) :
    ∀ᶠ X : ℝ in atTop, ∀ B : ℝ, 0 < B → B ≤ X^(12/25:ℝ) →
      (C*B)^(1/50:ℝ) ≤ X^(1/100:ℝ) := by
  filter_upwards [eventually_ge_atTop (1:ℝ),
    eventually_const_mul_rpow_le (show (6/625:ℝ) < 1/100 by norm_num) (C^(1/50:ℝ))]
    with X hX hgap
  intro B hB hBX
  have hXp : 0 < X := zero_lt_one.trans_le hX
  calc
    _ = C^(1/50:ℝ)*B^(1/50:ℝ) := Real.mul_rpow hC.le hB.le
    _ ≤ C^(1/50:ℝ)*(X^(12/25:ℝ))^(1/50:ℝ) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hB.le hBX (by norm_num)) (by positivity)
    _ = C^(1/50:ℝ)*X^(6/625:ℝ) := by rw [←Real.rpow_mul hXp.le]; norm_num
    _ ≤ _ := hgap

end CubicFirstMoment

end

end OAI
