import OAI.MeasureTheory.Falconer.Radial.RadialScaleWindow

namespace OAI

/-! # Compatible losses for the endpoint bad-triple estimate -/

namespace Falconer

 theorem exists_endpoint_radial_losses (h : ℕ) {ell a : ℝ}
    (hell : (h:ℝ) < ell) (ha : 0 < a) :
    ∃ H : ℕ, 0 < H ∧ ∃ b e : ℝ, 0 < b ∧ 0 < e ∧
      1/(H:ℝ) < a-2*b ∧ 0 < (ell-h)/(2*(H:ℝ))-2*(h:ℝ)*b-e := by
  obtain ⟨H₀,hH₀⟩ := exists_nat_gt (4/a)
  let H := H₀+1
  have hH : 0 < H := by dsimp [H]; omega
  have hHr : (0:ℝ) < H := by exact_mod_cast hH
  have hHa : 4/a < (H:ℝ) := by dsimp [H]; push_cast; linarith
  have hinv : 1/(H:ℝ) < a/4 := by
    apply (div_lt_iff₀ hHr).mpr
    have hh := (div_lt_iff₀ ha).mp hHa
    nlinarith
  let b := min (a/8) ((ell-h)/(32*((h:ℝ)+1)*(H:ℝ)))
  let e := (ell-h)/(16*(H:ℝ))
  have hb : 0 < b := by dsimp [b]; positivity
  have he : 0 < e := by dsimp [e]; positivity
  have hb₁ : b ≤ a/8 := min_le_left _ _
  have hb₂ : b ≤ (ell-h)/(32*((h:ℝ)+1)*(H:ℝ)) := min_le_right _ _
  have hprod : 2*(h:ℝ)*b ≤ (ell-h)/(16*(H:ℝ)) := by
    have hh : (h:ℝ) ≤ (h:ℝ)+1 := by linarith
    have ht := mul_le_mul_of_nonneg_left hb₂ (show 0 ≤ 2*((h:ℝ)+1) by positivity)
    have heq : 2*((h:ℝ)+1)*((ell-h)/(32*((h:ℝ)+1)*(H:ℝ))) =
        (ell-h)/(16*(H:ℝ)) := by field_simp; ring
    rw [heq] at ht
    exact (mul_le_mul_of_nonneg_right (by linarith : 2*(h:ℝ) ≤ 2*((h:ℝ)+1)) hb.le).trans ht
  refine ⟨H,hH,b,e,hb,he,by linarith,?_⟩
  have heq : (ell-h)/(2*(H:ℝ)) = 8*e := by dsimp [e]; ring
  rw [heq]
  change 0 < 8*e-2*(h:ℝ)*b-e
  change 2*(h:ℝ)*b ≤ e at hprod
  linarith

end Falconer

end OAI
