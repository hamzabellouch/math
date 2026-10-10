import OAI.NumberTheory.JointDickman.Counting.CoefficientMinorArc

namespace OAI

/-! # A power saving for the coefficient sum on the minor arcs -/

namespace JointDickman
open Filter
open scoped Topology

theorem minorArc_log_factor : ∀ᶠ B : ℕ in atTop,
    (Real.log ((B : ℝ)^10))^(3/2 : ℝ)/Real.sqrt ((B : ℝ)^10) ≤ 1/(B : ℝ) := by
  have hh := ((log_power_div_power_tendsto_zero (3/2) (by norm_num : (0 : ℝ) < 4)).const_mul
    ((10 : ℝ)^(3/2 : ℝ))).comp tendsto_natCast_atTop_atTop
  have hz : (10 : ℝ)^(3/2 : ℝ)*0 = 0 := mul_zero _
  rw [hz] at hh
  filter_upwards [hh.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_gt_atTop 1] with B hsmall hB
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (Nat.zero_lt_of_lt hB)
  have hlog0 : 0 ≤ Real.log (B : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ B))
  have hnum : (Real.log ((B : ℝ)^10))^(3/2 : ℝ) ≤ (B : ℝ)^4 := by
    rw [Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 10) hlog0]
    apply (div_le_one (pow_pos hB0 4)).mp
    convert hsmall using 1
    norm_num [Function.comp_def,mul_div_assoc]
  have hsqrt : Real.sqrt ((B : ℝ)^10) = (B : ℝ)^5 := by
    rw [show (B : ℝ)^10 = ((B : ℝ)^5)^2 by ring,Real.sqrt_sq (pow_nonneg hB0.le 5)]
  rw [hsqrt]
  calc
    _ ≤ (B : ℝ)^4/(B : ℝ)^5 := div_le_div_of_nonneg_right hnum (pow_nonneg hB0.le 5)
    _ = _ := by field_simp

theorem coefficient_minorArc_power_bound
    (hMV : PublishedInputs.MultiplicativeExponentialInput) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℕ in atTop,
      ∀ (Y : ℕ) (X θ : ℝ), 2 ≤ Y →
      (B : ℝ)/2 ≤ Real.log Y → (B : ℝ)^12 ≤ X →
      X ≤ (Y : ℝ)*(B : ℝ)^2 →
      ¬ InRationalArc θ ((B : ℝ)^12) ((B : ℝ)^13/X) →
      ‖coefficientAdditivePartialSum B Y θ‖ ≤ C*Y*(B : ℝ)^(-1/2+ε) := by
  obtain ⟨C,hC,hbound⟩ := coefficient_minorArc_bound hMV
  refine ⟨3*C,by positivity,?_⟩
  filter_upwards [coefficientScale_power hε,minorArc_log_factor,eventually_ge_atTop 2]
    with B hscale hlogfactor hB
  intro Y X θ hY hlog hX hYX hminor
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hY0 : (0 : ℝ) ≤ Y := Nat.cast_nonneg Y
  have hlogY : 0 < Real.log (Y : ℝ) := (half_pos hB0).trans_le hlog
  have hlogR : 0 ≤ Real.log ((B : ℝ)^10) := Real.log_nonneg
    (one_le_pow₀ (show (1 : ℝ) ≤ B by exact_mod_cast (by omega : 1 ≤ B)))
  have hterm : (Y : ℝ)/Real.log Y + Y*(Real.log ((B : ℝ)^10))^(3/2 : ℝ)/
      Real.sqrt ((B : ℝ)^10) ≤ 3*Y/(B : ℝ) := by
    calc
      _ ≤ (Y : ℝ)/((B : ℝ)/2)+(Y : ℝ)*(1/(B : ℝ)) := by
        apply add_le_add
        · exact div_le_div_of_nonneg_left hY0 (half_pos hB0) hlog
        · simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hlogfactor hY0
      _ = _ := by ring
  have hterm0 : 0 ≤ (Y : ℝ)/Real.log Y + Y*(Real.log ((B : ℝ)^10))^(3/2 : ℝ)/
      Real.sqrt ((B : ℝ)^10) := by positivity
  calc
    _ ≤ C*coefficientScale B*((Y : ℝ)/Real.log Y +
        Y*(Real.log ((B : ℝ)^10))^(3/2 : ℝ)/Real.sqrt ((B : ℝ)^10)) :=
      hbound B Y X θ hB hY hX hYX hminor
    _ ≤ C*(B : ℝ)^(1/2+ε)*(3*Y/(B : ℝ)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hscale hC.le) hterm hterm0 (by positivity)
    _ = _ := by
      have he : (B : ℝ)^(1/2+ε)/(B : ℝ) = (B : ℝ)^(-1/2+ε) := by
        calc
          _ = (B : ℝ)^(1/2+ε)/(B : ℝ)^(1 : ℝ) := by rw [Real.rpow_one]
          _ = _ := by rw [← Real.rpow_sub hB0]; congr 1; ring
      calc
        _ = 3*C*Y*((B : ℝ)^(1/2+ε)/(B : ℝ)) := by ring
        _ = _ := by rw [he]

end JointDickman

end OAI
