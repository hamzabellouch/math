import OAI.NumberTheory.Ostmann.Dirichlet.ZetaLargeHeight

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

namespace Ostmann.Dirichlet

@[simp] lemma zetaDiskPoint_im (t : ℝ) (rho : ℂ) :
    (zetaDiskPoint t rho).im = t + (5 / 4 : ℝ) * rho.im := by
  simp [zetaDiskPoint, zetaCenter]

lemma zetaDiskPoint_height_bounds {t : ℝ} (ht : 3 ≤ |t|) {rho : ℂ}
    (hr : ‖rho‖ ≤ 19 / 20) :
    1 ≤ |(zetaDiskPoint t rho).im| ∧
      Real.log (|(zetaDiskPoint t rho).im| + 6) ≤ 2 * Real.log (|t| + 6) := by
  have hi : |rho.im| ≤ 19 / 20 := (Complex.abs_im_le_norm rho).trans hr
  have hoff : |(5 / 4 : ℝ) * rho.im| ≤ 5 / 4 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 5 / 4)]
    linarith
  have habs : |(zetaDiskPoint t rho).im| ≤ |t| + 2 := by
    rw [zetaDiskPoint_im]
    have h := abs_add_le t ((5 / 4 : ℝ) * rho.im)
    linarith
  constructor
  · have h := abs_add_le ((zetaDiskPoint t rho).im) (-((5 / 4 : ℝ) * rho.im))
    have he : (zetaDiskPoint t rho).im + -((5 / 4 : ℝ) * rho.im) = t := by
      rw [zetaDiskPoint_im]
      ring
    rw [he, abs_neg] at h
    linarith
  · have h := Real.log_le_log (by positivity : 0 < |(zetaDiskPoint t rho).im| + 6)
      (show |(zetaDiskPoint t rho).im| + 6 ≤ (|t| + 6) ^ 2 by
        have := abs_nonneg t; nlinarith)
    rw [Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    exact h

theorem exists_zeta_large_height_zero_separation :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 / 100 ∧ ∀ sigma t : ℝ,
      3 ≤ |t| → 1 - a / Real.log (|t| + 6) ≤ sigma →
      riemannZeta ((sigma : ℂ) + (t : ℂ) * Complex.I) ≠ 0 ∧
      ∀ rho : ℂ, ‖rho‖ ≤ 19 / 20 → regularZeta (zetaDiskPoint t rho) = 0 →
        a / Real.log (|t| + 6) ≤ ‖((4 / 5 * (sigma - 2) : ℝ) : ℂ) - rho‖ := by
  obtain ⟨c, hc, hregion⟩ := exists_zeta_large_height_zero_free_region
  let a : ℝ := min (c / 8) (1 / 100)
  have ha : 0 < a := lt_min (by positivity) (by norm_num)
  have hac : a ≤ c / 8 := min_le_left _ _
  have ha100 : a ≤ 1 / 100 := min_le_right _ _
  refine ⟨a, ha, ha100, ?_⟩
  intro sigma t ht hs
  let H : ℝ := Real.log (|t| + 6)
  have hH : 1 ≤ H := zeta_height_ge_one t
  have hHp : 0 < H := by linarith
  constructor
  · apply hregion ((sigma : ℂ) + (t : ℂ) * Complex.I) (by simpa using (by linarith : 1 ≤ |t|))
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, mul_zero, sub_zero, add_zero,
      Complex.add_im, Complex.mul_im, mul_one, zero_add]
    have hh := div_le_div_of_nonneg_right (show a ≤ c by linarith) hHp.le
    change 1 - a / H ≤ sigma at hs
    change 1 - c / H ≤ sigma
    linarith
  · intro rho hr hz
    obtain ⟨hheight, hupper⟩ := zetaDiskPoint_height_bounds ht hr
    have hn : zetaDiskPoint t rho ≠ 1 := by
      intro he
      rw [he, Complex.one_im, abs_zero] at hheight
      norm_num at hheight
    have hzero : riemannZeta (zetaDiskPoint t rho) = 0 := by
      rw [regularZeta_eq_mul hn] at hz
      exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hn)
    have hZp : 0 < Real.log (|(zetaDiskPoint t rho).im| + 6) :=
      zero_lt_one.trans_le (zeta_height_ge_one _)
    have hdrop : c / (2 * H) ≤ c / Real.log (|(zetaDiskPoint t rho).im| + 6) :=
      div_le_div_of_nonneg_left hc.le hZp hupper
    have hzeroRe : (zetaDiskPoint t rho).re <
        1 - c / Real.log (|(zetaDiskPoint t rho).im| + 6) := by
      by_contra! h
      exact hregion (zetaDiskPoint t rho) hheight h hzero
    have ha4 : 4 * (a / H) ≤ c / (2 * H) := by
      have hh := div_le_div_of_nonneg_right (show 4 * a ≤ c / 2 by linarith) hHp.le
      convert hh using 1 <;> ring
    have hdiff : (5 / 4 : ℝ) * ((((4 / 5 * (sigma - 2) : ℝ) : ℂ)).re - rho.re) =
        sigma - (zetaDiskPoint t rho).re := by
      rw [Complex.ofReal_re, zetaDiskPoint_re]
      ring
    have har : 0 ≤ a / H := div_nonneg ha.le hHp.le
    have hsep : a / H ≤ (((4 / 5 * (sigma - 2) : ℝ) : ℂ)).re - rho.re := by
      change 1 - a / H ≤ sigma at hs
      nlinarith only [hs, hzeroRe, hdrop, ha4, hdiff, har]
    exact hsep.trans (by simpa only [Complex.sub_re] using
      (Complex.re_le_norm (((4 / 5 * (sigma - 2) : ℝ) : ℂ) - rho)))

end Ostmann.Dirichlet

end OAI
