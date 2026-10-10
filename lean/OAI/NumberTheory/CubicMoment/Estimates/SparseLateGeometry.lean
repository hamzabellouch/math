import OAI.NumberTheory.CubicMoment.Estimates.FixedScalePowers

namespace OAI

/-! The late-stop norm range in the manuscript supplies all length
hypotheses of the sparse cubic and model bounds, including fixed dyadic
dilations. -/
noncomputable section
open Filter
namespace CubicFirstMoment

lemma late_stop_rectangle_bounds {X A B D : ℝ} (hX : 1 ≤ X) (hD : 1 ≤ D)
    (hB : X^(35/100:ℝ) ≤ B) (hBhi : B ≤ X^(40/100:ℝ))
    (hA : A ≤ D*X/B) :
    A ≤ D*X^(65/100:ℝ) ∧ B ≤ X ∧
      A ≤ D*X^(2/3:ℝ) ∧ B ≤ D*X^(2/3:ℝ) ∧ A*B ≤ D*X := by
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hp : 0 < X^(35/100:ℝ) := Real.rpow_pos_of_pos hXp _
  have hBp : 0 < B := hp.trans_le hB
  have hquot : X/X^(35/100:ℝ) = X^(65/100:ℝ) := by
    nth_rw 1 [←Real.rpow_one X]
    rw [←Real.rpow_sub hXp]
    norm_num
  have hAa : A ≤ D*X^(65/100:ℝ) := by
    calc
      _ ≤ D*(X/B) := by simpa only [mul_div_assoc] using hA
      _ ≤ D*(X/X^(35/100:ℝ)) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hXp.le hp hB) (by linarith)
      _ = _ := by rw [hquot]
  refine ⟨hAa,?_,?_,?_,(le_div_iff₀ hBp).mp hA⟩
  · exact hBhi.trans (by simpa using
      Real.rpow_le_rpow_of_exponent_le hX (show (40/100:ℝ) ≤ 1 by norm_num))
  · exact hAa.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hX (by norm_num)) (by linarith))
  · apply hBhi.trans
    apply (Real.rpow_le_rpow_of_exponent_le hX (show (40/100:ℝ) ≤ 2/3 by norm_num)).trans
    exact le_mul_of_one_le_left (Real.rpow_nonneg hXp.le _) hD

lemma eventually_late_stop_rectangle_bounds {D : ℝ} (hD : 1 ≤ D) :
    ∀ᶠ X : ℝ in atTop, ∀ A B : ℝ,
      X^(35/100:ℝ) ≤ B → B ≤ X^(40/100:ℝ) → A ≤ D*X/B →
      A ≤ X ∧ B ≤ X ∧ A ≤ D*X^(2/3:ℝ) ∧
        B ≤ D*X^(2/3:ℝ) ∧ A*B ≤ D*X := by
  filter_upwards [eventually_ge_atTop (1:ℝ),
    eventually_const_mul_rpow_le (show (65/100:ℝ) < 1 by norm_num) D] with X hX hDX
  intro A B hB hBhi hA
  obtain ⟨ha,hb,has,hbs,hab⟩ := late_stop_rectangle_bounds hX hD hB hBhi hA
  exact ⟨ha.trans (by simpa only [Real.rpow_one] using hDX),hb,has,hbs,hab⟩

end CubicFirstMoment

end

end OAI
