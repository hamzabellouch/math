import OAI.NumberTheory.Ostmann.Construction.OriginalProductScale

namespace OAI

/-! # An integer endpoint scale compatible with every selected dyadic block -/

namespace Ostmann

open Filter

noncomputable def endpointBaseScale (T : ℝ) : ℝ := 7 * T ^ (8 / 5 : ℝ) / 4
noncomputable def endpointSize (T : ℝ) : ℕ := ⌊Real.exp (endpointBaseScale T)⌋₊
noncomputable def endpointLogScale (T : ℝ) : ℝ := Real.log (endpointSize T : ℝ)

private theorem two_rpow_three_fifths_le : (2 : ℝ) ^ (3 / 5 : ℝ) ≤ 8 / 5 := by
  apply (Real.rpow_le_rpow_iff (Real.rpow_nonneg (by norm_num) _) (by norm_num)
    (by norm_num : (0 : ℝ) < 5)).mp
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

theorem eventual_endpoint_scale :
    ∀ᶠ T : ℝ in atTop, 1 ≤ endpointSize T ∧
      Real.exp (endpointLogScale T) = (endpointSize T : ℝ) ∧
      T ≤ endpointLogScale T ∧ T ^ (3 / 2 : ℝ) ≤ endpointLogScale T ∧
      endpointLogScale T ≤ 2 * T ^ 2 ∧
      ∀ V : ℝ, T - Real.log 2 ≤ V → V ≤ 2 * T →
        T / 2 ≤ V ∧ 0 < V ∧
        V ^ (8 / 5 : ℝ) / 2 ≤ endpointLogScale T ∧
        endpointLogScale T ≤ (9 / 5 : ℝ) * V ^ (8 / 5 : ℝ) := by
  filter_upwards [(tendsto_rpow_atTop (show (0 : ℝ) < 8 / 5 by norm_num)).eventually_ge_atTop
      (20 * Real.log 2), eventually_ge_atTop (max 1 (100 * Real.log 2))] with T hbig hT
  have hT1 : 1 ≤ T := (le_max_left _ _).trans hT
  have hTp : 0 < T := by linarith
  have hp1 : 1 ≤ T ^ (8 / 5 : ℝ) := Real.one_le_rpow hT1 (by norm_num)
  have hs1 : 1 ≤ endpointBaseScale T := by dsimp [endpointBaseScale]; linarith
  have hbounds := floor_exp_log_bounds (endpointBaseScale T) hs1
  have hLlo : (17 / 10 : ℝ) * T ^ (8 / 5 : ℝ) ≤ endpointLogScale T := by
    have hh := hbounds.2.1
    change endpointBaseScale T - Real.log 2 ≤ endpointLogScale T at hh
    dsimp [endpointBaseScale] at hh
    linarith
  have hLhi : endpointLogScale T ≤ (7 / 4 : ℝ) * T ^ (8 / 5 : ℝ) := by
    have hh := hbounds.2.2
    change endpointLogScale T ≤ endpointBaseScale T at hh
    dsimp [endpointBaseScale] at hh
    linarith
  have hTpow : T ≤ T ^ (8 / 5 : ℝ) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hT1
      (show (1 : ℝ) ≤ 8 / 5 by norm_num)
  have hT32 : T ^ (3 / 2 : ℝ) ≤ T ^ (8 / 5 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT1 (by norm_num)
  have hT2 : T ^ (8 / 5 : ℝ) ≤ T ^ 2 := by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le hT1 (show (8 / 5 : ℝ) ≤ 2 by norm_num)
  have hsize0 : (0 : ℝ) < endpointSize T := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) hbounds.1)
  refine ⟨hbounds.1, Real.exp_log hsize0, by linarith, by linarith, by nlinarith, ?_⟩
  intro V hVlo hVhi
  have hTbig := (le_max_right _ _).trans hT
  have hV99 : (99 / 100 : ℝ) * T ≤ V := by linarith
  have hVhalf : T / 2 ≤ V := by linarith
  have hVp : 0 < V := by linarith
  have hVupper : V ^ (8 / 5 : ℝ) ≤ (16 / 5 : ℝ) * T ^ (8 / 5 : ℝ) := by
    calc
      _ ≤ (2 * T) ^ (8 / 5 : ℝ) := Real.rpow_le_rpow hVp.le hVhi (by norm_num)
      _ = (2 : ℝ) ^ (8 / 5 : ℝ) * T ^ (8 / 5 : ℝ) := Real.mul_rpow (by norm_num) hTp.le
      _ ≤ _ := by
        rw [show (8 / 5 : ℝ) = 1 + 3 / 5 by norm_num, Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
        nlinarith [mul_nonneg (sub_nonneg.mpr two_rpow_three_fifths_le) (Real.rpow_nonneg hTp.le (8 / 5 : ℝ))]
  have hVlower : (9801 / 10000 : ℝ) * T ^ (8 / 5 : ℝ) ≤ V ^ (8 / 5 : ℝ) := by
    have hc : (9801 / 10000 : ℝ) ≤ (99 / 100 : ℝ) ^ (8 / 5 : ℝ) := by
      have hh := Real.rpow_le_rpow_of_exponent_ge (by norm_num : (0 : ℝ) < 99 / 100)
        (by norm_num : (99 / 100 : ℝ) ≤ 1) (show (8 / 5 : ℝ) ≤ 2 by norm_num)
      norm_num at hh ⊢
      exact hh
    calc
      _ ≤ (99 / 100 : ℝ) ^ (8 / 5 : ℝ) * T ^ (8 / 5 : ℝ) :=
        mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hTp.le _)
      _ = ((99 / 100 : ℝ) * T) ^ (8 / 5 : ℝ) := (Real.mul_rpow (by norm_num) hTp.le).symm
      _ ≤ _ := Real.rpow_le_rpow (by positivity) hV99 (by norm_num)
  refine ⟨hVhalf, hVp, ?_, ?_⟩ <;> nlinarith

end Ostmann

end OAI
