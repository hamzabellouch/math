import OAI.NumberTheory.CubicMoment.Estimates.SemiprimeRange

namespace OAI

/-! A strict grouping gap above one third implies the actual logarithmic
upper-length condition in the published-input bilinear theorem. -/
noncomputable section
open Filter
namespace CubicFirstMoment

theorem ordinary_group_upper_range {δ C : ℝ} (hδ : 0 < δ) (hC : 0 < C) (G : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ A B : ℝ,
      X^(1/3+δ:ℝ) ≤ B → A*B ≤ C*X → A ≤ B^2/(1+Real.log B)^G := by
  let α : ℝ := 1/3+δ
  let ε : ℝ := δ/α
  have hα : 0 < α := by dsimp [α]; linarith
  have hε : 0 < ε := div_pos hδ hα
  have hε1 : ε < 1 := (div_lt_one hα).mpr (by dsimp [α]; linarith)
  have hpower : α*(3-ε) = 1+2*δ := by
    dsimp [ε]
    field_simp [hα.ne']
    dsimp [α]
    ring
  obtain ⟨B₀,hB₀⟩ := eventually_atTop.mp (overlap_power_log_saving hε G 0)
  filter_upwards [eventually_ge_atTop (1:ℝ),
    (tendsto_rpow_atTop hα).eventually_ge_atTop B₀,
    eventually_const_mul_rpow_le (by linarith : (1:ℝ) < 1+2*δ) C]
    with X hX hXB hgap
  intro A B hB hAB
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hB1 : 1 ≤ B := (Real.one_le_rpow hX hα.le).trans hB
  have hBp : 0 < B := zero_lt_one.trans_le hB1
  have hL : 0 < 1+Real.log B := by linarith [Real.log_nonneg hB1]
  have hlog : (1+Real.log B)^G ≤ B^ε := by
    have hh := hB₀ B (hXB.trans hB)
    simpa only [Nat.mul_zero,pow_zero,div_one,one_mul] using
      (div_le_iff₀ (Real.rpow_pos_of_pos hBp ε)).mp hh
  have hp : X^(1+2*δ) ≤ B^(3-ε) := by
    have hh := Real.rpow_le_rpow (Real.rpow_nonneg hXp.le α) hB (by linarith : 0 ≤ 3-ε)
    rw [←Real.rpow_mul hXp.le,hpower] at hh
    exact hh
  have hCX : C*X ≤ B^(3-ε) := by
    have hh : C*X ≤ X^(1+2*δ) := by simpa only [Real.rpow_one] using hgap
    exact hh.trans hp
  have hm : (A*B)*(1+Real.log B)^G ≤ B^3 := by
    calc
      _ ≤ (C*X)*(1+Real.log B)^G := mul_le_mul_of_nonneg_right hAB (pow_nonneg hL.le _)
      _ ≤ (C*X)*B^ε := mul_le_mul_of_nonneg_left hlog (mul_nonneg hC.le hXp.le)
      _ ≤ B^(3-ε)*B^ε := mul_le_mul_of_nonneg_right hCX (Real.rpow_nonneg hBp.le _)
      _ = B^3 := by rw [←Real.rpow_add hBp]; norm_num
  apply (le_div_iff₀ (pow_pos hL G)).mpr
  apply (mul_le_mul_iff_right₀ hBp).mp
  convert hm using 1 <;> ring

end CubicFirstMoment

end

end OAI
