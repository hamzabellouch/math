import OAI.NumberTheory.CubicMoment.Estimates.TailPrimeTailGeometry
import OAI.NumberTheory.CubicMoment.Estimates.FixedScalePowers

namespace OAI

/-! The enlarged conductor range overlaps the published-Hecke height
range. Fixed dyadic support constants are absorbed by a strict power gap. -/
noncomputable section
open Filter
namespace CubicFirstMoment

theorem eventually_tailPrime_small_group_length {D K : ℝ} (hD : 0 < D) (hK : 0 < K) :
    ∀ᶠ X : ℝ in atTop, ∀ A B : ℝ, 0 < B → X/D ≤ A*B →
      B ≤ X^(12/25:ℝ) → K*B^(27/25:ℝ) ≤ A := by
  filter_upwards [eventually_ge_atTop (1:ℝ),
    eventually_const_mul_rpow_le (show (624/625:ℝ) < 1 by norm_num) (D*K)]
    with X hX hgap
  intro A B hB hAB hBX
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hpow : B^(52/25:ℝ) ≤ X^(624/625:ℝ) := by
    calc
      _ ≤ (X^(12/25:ℝ))^(52/25:ℝ) :=
        Real.rpow_le_rpow hB.le hBX (by norm_num)
      _ = _ := by rw [←Real.rpow_mul hXp.le]; norm_num
  have hprod : D*(B*(K*B^(27/25:ℝ))) ≤ D*(A*B) := by
    calc
      _ = (D*K)*B^(52/25:ℝ) := by
        have he : B*B^(27/25:ℝ) = B^(52/25:ℝ) := by
          calc
            _ = B^(1:ℝ)*B^(27/25:ℝ) := by rw [Real.rpow_one]
            _ = _ := by rw [←Real.rpow_add hB]; norm_num
        calc
          _ = (D*K)*(B*B^(27/25:ℝ)) := by ring
          _ = _ := by rw [he]
      _ ≤ (D*K)*X^(624/625:ℝ) := mul_le_mul_of_nonneg_left hpow (mul_pos hD hK).le
      _ ≤ X := by simpa only [Real.rpow_one] using hgap
      _ ≤ D*(A*B) := by
        have hh := (div_le_iff₀ hD).mp hAB
        nlinarith
  have he : D*B*(K*B^(27/25:ℝ)) ≤ D*B*A := by nlinarith [hprod]
  exact (mul_le_mul_iff_right₀ (mul_pos hD hB)).mp he

lemma tailPrime_large_group_height {X B η : ℝ} (hX : 1 ≤ X)
    (hη : η ≤ 1/1500) (hB : X^(12/25:ℝ) ≤ B) :
    X^(1/6+η) ≤ B^(7/20:ℝ) := by
  calc
    _ ≤ X^((12/25:ℝ)*(7/20)) :=
      Real.rpow_le_rpow_of_exponent_le hX (by linarith)
    _ = (X^(12/25:ℝ))^(7/20:ℝ) := Real.rpow_mul (zero_le_one.trans hX) _ _
    _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg (zero_le_one.trans hX) _) hB (by norm_num)

end CubicFirstMoment

end

end OAI
