import OAI.NumberTheory.JointDickman.Analysis.ZetaPoleBranch
import PrimeNumberTheoremAnd.ZetaBounds

namespace OAI

/-! # A quantitative zero-free region for the finite contour

The logarithmic ninth-power zero-free region suffices for fixed-order
contour estimates.
-/
namespace JointDickman
open Set

noncomputable def zetaContourWidth (A T : ℝ) : ℝ := A/(1+Real.log (T+3))^9

theorem zeta_contour_zero_free : ∃ A : ℝ, 0 < A ∧ A ≤ 1/4 ∧
    ∀ T : ℝ, 0 ≤ T → 0 < zetaContourWidth A T ∧ zetaContourWidth A T ≤ 1/4 ∧
      ∀ s : ℂ, 1-zetaContourWidth A T ≤ s.re → |s.im| ≤ T → riemannZeta s ≠ 0 := by
  obtain ⟨σ₀,hσ₀,hsmall⟩ := ZetaNoZerosInBox 3
  obtain ⟨A₀,hA₀,hlarge⟩ := ZetaZeroFree9
  let A := min (1/4:ℝ) (min (1-σ₀) A₀)
  have hA : 0 < A := lt_min (by norm_num) (lt_min (by linarith) hA₀.1)
  have hA4 : A ≤ 1/4 := min_le_left _ _
  have hAσ : A ≤ 1-σ₀ := (min_le_right _ _).trans (min_le_left _ _)
  have hAA : A ≤ A₀ := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨A,hA,hA4,fun T hT => ?_⟩
  have hlog : 0 < Real.log (T+3) := Real.log_pos (by linarith)
  have hd : 0 < (1+Real.log (T+3))^9 := by positivity
  have hd1 : 1 ≤ (1+Real.log (T+3))^9 := one_le_pow₀ (by linarith)
  have hwA : zetaContourWidth A T ≤ A := by
    unfold zetaContourWidth
    exact div_le_self hA.le hd1
  refine ⟨div_pos hA hd,hwA.trans hA4,fun s hs ht => ?_⟩
  have hs0 : σ₀ ≤ s.re := by linarith
  have heq : (s.re:ℂ)+(s.im:ℂ)*Complex.I = s := Complex.re_add_im s
  rcases le_or_gt |s.im| 3 with ht3 | ht3
  · rw [←heq]
    exact hsmall s.im ht3 s.re hs0
  · rcases lt_or_ge s.re 1 with hs1 | hs1
    · have hltlog : 0 < Real.log |s.im| := Real.log_pos (by linarith)
      have hl : Real.log |s.im| ≤ 1+Real.log (T+3) := by
        have hh := Real.log_le_log (by positivity : 0 < |s.im|) (show |s.im| ≤ T+3 by linarith)
        linarith
      have hwidth : zetaContourWidth A T ≤ A₀/(Real.log |s.im|)^9 := by
        unfold zetaContourWidth
        exact div_le_div₀ hA₀.1.le hAA (by positivity) (pow_le_pow_left₀ hltlog.le hl 9)
      rw [←heq]
      apply hlarge s.re s.im ht3
      constructor
      · simpa only [show (9:ℝ) = (9:ℕ) by norm_num,Real.rpow_natCast] using
          (show 1-A₀/(Real.log |s.im|)^9 ≤ s.re by linarith)
      · exact hs1
    · rcases hs1.eq_or_lt with hs1 | hs1
      · rw [←heq,←hs1]
        exact ZetaNoZerosOn1Line s.im
      · exact riemannZeta_ne_zero_of_one_lt_re hs1

end JointDickman

end OAI
