import OAI.NumberTheory.CubicMoment.Estimates.PrimeIndicatorPowers
import OAI.NumberTheory.CubicMoment.Estimates.SquarefreeTwists

namespace OAI

/-! The explicit small-modulus margins for adding the second cubic conductor. -/
noncomputable section
open Filter
namespace CubicFirstMoment

lemma small_second_modulus {Y δ : ℝ} (hY : 1 ≤ Y) (hδ : δ ≤ 1/400000)
    (h9 : 9 ≤ Y^δ) {q b : Eisenstein}
    (hq : norm q ≤ Y^δ) (hb : norm b ≤ Y^δ) :
    norm (q*(3*(1*b))) ≤ Y^(1/100000:ℝ) := by
  have hYp : 0 < Y := zero_lt_one.trans_le hY
  have h3 : norm (3:Eisenstein) = 9 := by
    change Complex.normSq (3:ℂ) = 9
    norm_num
  calc
    norm (q*(3*(1*b))) = 9*(norm q*norm b) := by
      rw [one_mul,norm_mul_eq,norm_mul_eq,h3]
      ring
    _ ≤ 9*(Y^δ*Y^δ) := by gcongr; exact norm_nonneg b
    _ ≤ Y^δ*(Y^δ*Y^δ) := by gcongr
    _ = Y^(3*δ) := by rw [← Real.rpow_add hYp,← Real.rpow_add hYp]; congr 1; ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hY (by linarith)

lemma small_second_conductor_absorption {e δ : ℝ} (he : 0 < e) (hδ : 0 < δ)
    (hδe : δ ≤ e/4) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ Y : ℝ, T ≤ Y →
      9 ≤ Y^δ ∧ 18*Y^δ*Y^(7/3-e) ≤ Y^(7/3-e/2) := by
  obtain ⟨T₀,hT₀⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop hδ).eventually_ge_atTop (9:ℝ))
  obtain ⟨T₁,hT₁⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (show 0 < e/4 by positivity)).eventually_ge_atTop (18:ℝ))
  refine ⟨max 1 (max T₀ T₁),le_max_left _ _,?_⟩
  intro Y hY
  have hY1 : 1 ≤ Y := (le_max_left _ _).trans hY
  have hYp : 0 < Y := zero_lt_one.trans_le hY1
  refine ⟨hT₀ Y ((le_max_left _ _).trans ((le_max_right _ _).trans hY)),?_⟩
  calc
    _ ≤ Y^(e/4)*Y^δ*Y^(7/3-e) := by
      gcongr
      exact hT₁ Y ((le_max_right _ _).trans ((le_max_right _ _).trans hY))
    _ = Y^(e/4+δ+(7/3-e)) := by rw [← Real.rpow_add hYp,← Real.rpow_add hYp]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hY1 (by linarith)

end CubicFirstMoment

end

end OAI
