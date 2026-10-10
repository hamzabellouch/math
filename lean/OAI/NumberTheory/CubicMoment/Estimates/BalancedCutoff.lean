import OAI.NumberTheory.CubicMoment.Estimates.NaturalDualCutoff

namespace OAI

/-! Natural dual length for balanced conductors at height Y^0.37. -/
noncomputable section
open Filter
namespace CubicFirstMoment

theorem eventual_balanced_natural_cutoff :
    ∃ Y₀ : ℝ, 1 ≤ Y₀ ∧ ∀ Y N B Z t : ℝ, Y₀ ≤ Y → 0 ≤ N → 0 ≤ B →
      N ≤ Y^(17/50:ℝ) → B ≤ Y^(171/500:ℝ) →
      Y^(999/1000:ℝ) ≤ Z → |t| ≤ Y^(37/100:ℝ) →
      ((243*N*B/(2*Real.pi)^2)*(1+|t|)^2)/(Z*Y^(1/2:ℝ)) ≤ Y^(-(1/1000:ℝ)) := by
  obtain ⟨T,hT⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (show (0:ℝ) < 76/1000 by norm_num)).eventually_ge_atTop (972:ℝ))
  refine ⟨max 1 T,le_max_left _ _,?_⟩
  intro Y N B Z t hY hN hB hNY hBY hZY ht
  have hY1 : 1 ≤ Y := (le_max_left _ _).trans hY
  have hY0 : 0 < Y := zero_lt_one.trans_le hY1
  have hscale : 972 ≤ Y^(76/1000:ℝ) := hT Y ((le_max_right _ _).trans hY)
  have hZ0 : 0 < Z := (Real.rpow_pos_of_pos hY0 _).trans_le hZY
  have hπ : (1:ℝ) ≤ (2*Real.pi)^2 := by have := Real.pi_gt_three; nlinarith
  have ht' : 1+|t| ≤ 2*Y^(37/100:ℝ) := by
    have := Real.one_le_rpow hY1 (by norm_num : (0:ℝ) ≤ 37/100)
    linarith
  have htpow : (1+|t|)^2 ≤ 4*Y^(37/50:ℝ) := by
    have h := pow_le_pow_left₀ (by positivity : 0 ≤ 1+|t|) ht' 2
    have he : (Y^(37/100:ℝ))^2 = Y^(37/50:ℝ) := by
      rw [← Real.rpow_mul_natCast hY0.le]
      norm_num
    simpa only [mul_pow,he,show (2:ℝ)^2 = 4 by norm_num] using h
  have hNB : N*B ≤ Y^(341/500:ℝ) := by
    calc
      _ ≤ Y^(17/50:ℝ)*Y^(171/500:ℝ) :=
        mul_le_mul hNY hBY hB (Real.rpow_nonneg hY0.le _)
      _ = _ := by rw [← Real.rpow_add hY0]; norm_num
  have hnum : (243*N*B/(2*Real.pi)^2)*(1+|t|)^2 ≤ 972*Y^(711/500:ℝ) := by
    calc
      _ ≤ (243*(N*B))*(4*Y^(37/50:ℝ)) := by
        apply mul_le_mul _ htpow (sq_nonneg _) (by positivity)
        simpa only [mul_assoc] using div_le_self (by positivity : 0 ≤ 243*N*B) hπ
      _ ≤ (243*Y^(341/500:ℝ))*(4*Y^(37/50:ℝ)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hNB (by norm_num)) (by positivity)
      _ = 972*(Y^(341/500:ℝ)*Y^(37/50:ℝ)) := by ring
      _ = _ := by rw [← Real.rpow_add hY0]; norm_num
  have hden : Y^(1499/1000:ℝ) ≤ Z*Y^(1/2:ℝ) := by
    calc
      _ = Y^(999/1000:ℝ)*Y^(1/2:ℝ) := by rw [← Real.rpow_add hY0]; norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_right hZY (Real.rpow_nonneg hY0.le _)
  calc
    _ ≤ (972*Y^(711/500:ℝ))/Y^(1499/1000:ℝ) :=
      div_le_div₀ (by positivity) hnum (Real.rpow_pos_of_pos hY0 _) hden
    _ = 972*Y^(-(77/1000:ℝ)) := by
      rw [mul_div_assoc,← Real.rpow_sub hY0]
      norm_num
    _ ≤ Y^(76/1000:ℝ)*Y^(-(77/1000:ℝ)) :=
      mul_le_mul_of_nonneg_right hscale (Real.rpow_nonneg hY0.le _)
    _ = _ := by rw [← Real.rpow_add hY0]; norm_num

end CubicFirstMoment

end

end OAI
