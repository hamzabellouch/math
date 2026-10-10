import OAI.NumberTheory.JointDickman.Amplification.MinorArcApproximation

namespace OAI

/-! # The actual coefficient sum off the manuscript's major arcs -/

namespace JointDickman

theorem coefficient_minorArc_bound (hMV : PublishedInputs.MultiplicativeExponentialInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B Y : ℕ) (X θ : ℝ), 2 ≤ B → 2 ≤ Y →
      (B : ℝ)^12 ≤ X → X ≤ (Y : ℝ)*(B : ℝ)^2 →
      ¬ InRationalArc θ ((B : ℝ)^12) ((B : ℝ)^13/X) →
      ‖coefficientAdditivePartialSum B Y θ‖ ≤
        C*coefficientScale B*((Y : ℝ)/Real.log Y +
          Y*(Real.log ((B : ℝ)^10))^(3/2 : ℝ)/Real.sqrt ((B : ℝ)^10)) := by
  obtain ⟨C,hC,hbound⟩ := coefficient_additive_partial_sum_bound hMV
  refine ⟨C,hC,?_⟩
  intro B Y X θ hB hY hX hYX hminor
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast (show 1 ≤ B by omega)
  have hB2 : (2 : ℝ) ≤ B := by exact_mod_cast hB
  have hB0 : (0 : ℝ) < B := by linarith
  have hX0 : 0 < X := (pow_pos hB0 12).trans_le hX
  have hm : ¬ InRationalArc θ ((B : ℝ)^12) ((B : ℝ)^12/X) := by
    rintro ⟨r,hr,he⟩
    apply hminor
    refine ⟨r,hr,he.trans ?_⟩
    exact div_le_div_of_nonneg_right (pow_le_pow_right₀ hB1 (by norm_num : 12 ≤ 13)) hX0.le
  obtain ⟨r,hrlo,hrhi,happrox⟩ := minorArc_rational_approximation (pow_pos hB0 12) hX hm
  have hR : (2 : ℝ) ≤ (B : ℝ)^10 := hB2.trans (le_self_pow₀ hB1 (by norm_num : 10 ≠ 0))
  have hRq : (B : ℝ)^10 ≤ r.den :=
    (pow_le_pow_right₀ hB1 (by norm_num : 10 ≤ 12)).trans hrlo.le
  have hqY : (r.den : ℝ) ≤ (Y : ℝ)/(B : ℝ)^10 := by
    refine hrhi.trans ?_
    calc
      _ ≤ ((Y : ℝ)*(B : ℝ)^2)/(B : ℝ)^12 :=
        div_le_div_of_nonneg_right hYX (pow_nonneg hB0.le 12)
      _ = _ := by field_simp
  exact hbound B Y r.den r.num θ ((B : ℝ)^10) hY r.pos r.reduced
    (by simpa only [Rat.cast_def] using happrox) hR hRq hqY

end JointDickman

end OAI
