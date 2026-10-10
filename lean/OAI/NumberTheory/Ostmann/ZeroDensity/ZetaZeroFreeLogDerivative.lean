import OAI.NumberTheory.Ostmann.ZeroDensity.ZetaZeroFreeRegion
import OAI.NumberTheory.Ostmann.ZeroDensity.ZetaLocalSeparation

namespace OAI

/-! # A logarithmic-squared bound for the regularized zeta function -/

namespace Ostmann

open Complex

theorem zeta_zero_free_logDeriv_data : ∃ c C : ℝ,
    0 < c ∧ c ≤ 1 / 4 ∧ 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      ∀ s : ℂ, 1 - c / (Real.log (T + 4) + 1) ≤ s.re → s.re ≤ 2 → |s.im| ≤ T →
        regularizedZeta s ≠ 0 ∧ ‖logDeriv regularizedZeta s‖ ≤
          C * (Real.log (T + 4) + 1) ^ 2 := by
  obtain ⟨c0, hc0, _, hregion⟩ := regularizedZeta_zero_free_region
  obtain ⟨B, hB, hbound⟩ := zeta_local_logDeriv_separated
  let c := min (c0 / 4) (1 / 4)
  have hc : 0 < c := lt_min (by positivity) (by norm_num)
  have hcc : 4 * c ≤ c0 := by
    have hh := min_le_left (c0 / 4) (1 / 4)
    dsimp [c]
    linarith
  have hc4 : c ≤ 1 / 4 := min_le_right _ _
  refine ⟨c, B * (1 + c⁻¹), hc, hc4, by positivity, ?_⟩
  intro T hT s hs hs2 ht
  let H := Real.log (T + 4) + 1
  have hH : 1 ≤ H := by
    have hh := Real.log_nonneg (show 1 ≤ T + 4 by linarith)
    dsimp [H]
    linarith
  have hHp : 0 < H := by linarith
  let δ := c / H
  have hδ : 0 < δ := div_pos hc hHp
  have hδ4 : δ ≤ 1 / 4 := by
    calc
      c / H ≤ c / 1 := div_le_div_of_nonneg_left hc.le (by norm_num) hH
      _ ≤ 1 / 4 := by simpa using hc4
  change 1 - δ ≤ s.re at hs
  have hgap (ρ : ℂ) (hρ : regularizedZeta ρ = 0) (hρt : |ρ.im| ≤ T + 2) :
      4 * δ ≤ 1 - ρ.re := by
    have hden : 0 < Real.log (|ρ.im| + 2) + 1 := by
      have hh := Real.log_nonneg (show 1 ≤ |ρ.im| + 2 by linarith [abs_nonneg ρ.im])
      linarith
    have hd : Real.log (|ρ.im| + 2) + 1 ≤ H := by
      dsimp [H]
      exact add_le_add (Real.log_le_log (by positivity) (by linarith)) le_rfl
    calc
      4 * δ ≤ c0 / H := by
        dsimp [δ]
        rw [← mul_div_assoc]
        exact div_le_div_of_nonneg_right hcc hHp.le
      _ ≤ c0 / (Real.log (|ρ.im| + 2) + 1) := div_le_div_of_nonneg_left hc0.le hden hd
      _ ≤ 1 - ρ.re := hregion ρ hρ
  have hne : regularizedZeta s ≠ 0 := by
    intro he
    have hh := hgap s he (by linarith)
    linarith
  refine ⟨hne, ?_⟩
  let w : ℂ := s - characterZeroCenter s.im
  have hwval : w = ((s.re - 2 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [w, characterZeroCenter]
  have hw : ‖w‖ ≤ 5 / 4 := by
    rw [hwval, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    linarith
  have hf : zetaAtHeight s.im w ≠ 0 := by
    simpa only [zetaAtHeight, w, sub_add_cancel] using hne
  have hsep (z : ℂ) (hz : z ∈ zetaDiskZeros s.im) : δ ≤ ‖w - z‖ := by
    have hzero : regularizedZeta (z + characterZeroCenter s.im) = 0 :=
      ((mem_zetaDiskZeros s.im z).mp hz).2
    have hzi := Complex.abs_im_le_norm z
    have hzn := ((mem_zetaDiskZeros s.im z).mp hz).1
    have htri := abs_add_le z.im s.im
    have hzt : |(z + characterZeroCenter s.im).im| ≤ T + 2 := by
      simp only [Complex.add_im, characterZeroCenter_im]
      linarith
    have hh := hgap (z + characterZeroCenter s.im) hzero hzt
    have hre : δ ≤ (w - z).re := by
      rw [hwval]
      simp only [Complex.sub_re, Complex.ofReal_re]
      simp only [Complex.add_re, characterZeroCenter_re] at hh
      linarith
    exact hre.trans (Complex.re_le_norm _)
  have hb := hbound s.im w δ hw hf hδ hsep
  rw [zetaAtHeight_logDeriv_translate, show w + characterZeroCenter s.im = s by
    dsimp [w]; abel] at hb
  have hlog : Real.log (|s.im| + 2) ≤ H := by
    have hh : Real.log (|s.im| + 2) ≤ Real.log (T + 4) :=
      Real.log_le_log (by positivity) (by linarith)
    dsimp [H]
    linarith
  have hcost : 1 + δ⁻¹ ≤ H * (1 + c⁻¹) := by
    have he : δ⁻¹ = H * c⁻¹ := by dsimp [δ]; rw [inv_div]; ring
    rw [he]
    nlinarith
  calc
    _ ≤ B * H * (H * (1 + c⁻¹)) := hb.trans
      (mul_le_mul (mul_le_mul_of_nonneg_left hlog hB.le) hcost (by positivity) (by positivity))
    _ = _ := by dsimp [H]; ring

end Ostmann

end OAI
