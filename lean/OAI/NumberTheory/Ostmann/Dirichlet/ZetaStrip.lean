import OAI.NumberTheory.Ostmann.Dirichlet.ZetaCompactStrip
import OAI.NumberTheory.Ostmann.Dirichlet.ZetaStripBound

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

open Set
namespace Ostmann.Dirichlet

lemma zeta_height_le_twice_log {t : ℝ} (ht : 3 < |t|) :
    Real.log (|t| + 6) ≤ 2 * Real.log |t| := by
  have h := Real.log_le_log (by positivity : 0 < |t| + 6)
    (show |t| + 6 ≤ |t| ^ 2 by nlinarith)
  rw [Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  exact h

theorem exists_zeta_log_derivative_bounded_and_holomorphic :
    ∃ A C : ℝ, 0 < C ∧ A ∈ Ioc 0 (1 / 2) ∧
      (∀ sigma t : ℝ, 3 < |t| → 1 - A / Real.log |t| ≤ sigma →
        ‖deriv riemannZeta ((sigma : ℂ) + (t : ℂ) * Complex.I) /
            riemannZeta ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * (Real.log |t|) ^ 9) ∧
      ∀ T : ℝ, 3 ≤ T →
        DifferentiableOn ℂ (fun s => deriv riemannZeta s / riemannZeta s)
          (((Icc (1 - A / Real.log T) 2) ×ℂ Icc (-T) T) \ {1}) := by
  obtain ⟨a, ha, ha100, C, hC, hstrip⟩ := exists_zeta_large_height_strip_bound
  obtain ⟨δ, hδ, hcompact⟩ := exists_regularZeta_compact_zero_free_strip 3
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  let A : ℝ := min (a / 2) (min (δ * Real.log 3) (1 / 4))
  have hA : 0 < A := lt_min (by positivity) (lt_min (by positivity) (by norm_num))
  have hAa : A ≤ a / 2 := min_le_left _ _
  have hAδ : A ≤ δ * Real.log 3 := (min_le_right _ _).trans (min_le_left _ _)
  have hA4 : A ≤ 1 / 4 := (min_le_right _ _).trans (min_le_right _ _)
  have hM := absoluteMangoldtTwo_nonneg
  have hwidth {t : ℝ} (ht : 3 < |t|) : A / Real.log |t| ≤ a / Real.log (|t| + 6) := by
    have hl : 0 < Real.log |t| := Real.log_pos (by linarith)
    have hh : 0 < Real.log (|t| + 6) := zero_lt_one.trans_le (zeta_height_ge_one t)
    calc
      _ ≤ (a / 2) / Real.log |t| := div_le_div_of_nonneg_right hAa hl.le
      _ = a / (2 * Real.log |t|) := by ring
      _ ≤ _ := div_le_div_of_nonneg_left ha.le hh (zeta_height_le_twice_log ht)
  refine ⟨A, 4 * C + absoluteMangoldtTwo + 1, by positivity, ⟨hA, by linarith⟩, ?_, ?_⟩
  · intro sigma t ht hs
    have hl : 1 ≤ Real.log |t| :=
      ((Real.lt_log_iff_exp_lt (by linarith : 0 < |t|)).mpr
        (Real.exp_one_lt_three.trans ht)).le
    have hpow : (Real.log |t|) ^ 2 ≤ (Real.log |t|) ^ 9 :=
      pow_le_pow_right₀ hl (by norm_num)
    have hpow1 : 1 ≤ (Real.log |t|) ^ 9 := one_le_pow₀ hl
    by_cases hs2 : sigma ≤ 2
    · have hw := hwidth ht
      have hb := (hstrip sigma t ht.le (by linarith) hs2).2
      have hH := zeta_height_ge_one t
      have hHle := zeta_height_le_twice_log ht
      have hsq : (Real.log (|t| + 6)) ^ 2 ≤ 4 * (Real.log |t|) ^ 2 := by nlinarith
      have hh := mul_le_mul_of_nonneg_left hsq hC.le
      have hh' := mul_le_mul_of_nonneg_left hpow (show 0 ≤ 4 * C by positivity)
      nlinarith [mul_nonneg hM (show 0 ≤ (Real.log |t|) ^ 9 by positivity)]
    · have hb := norm_log_derivative_re_ge_two (1 : DirichletCharacter ℂ 1)
        (s := (sigma : ℂ) + (t : ℂ) * Complex.I) (by simpa using (le_of_not_ge hs2))
      rw [DirichletCharacter.LFunction_modOne_eq] at hb
      have hh := mul_le_mul_of_nonneg_left hpow1 hM
      have hc := mul_nonneg (show 0 ≤ 4 * C + 1 by positivity)
        (show 0 ≤ (Real.log |t|) ^ 9 by positivity)
      nlinarith
  · intro T hT s hs
    have hs1 : s ≠ 1 := hs.2
    have hre := hs.1.1.1
    have him : |s.im| ≤ T := abs_le.mpr hs.1.2
    have hlT : 0 < Real.log T := Real.log_pos (by linarith)
    have hn : riemannZeta s ≠ 0 := by
      by_cases ht : 3 < |s.im|
      · have hlt : 0 < Real.log |s.im| := Real.log_pos (by linarith)
        have hlog := Real.log_le_log (by linarith : 0 < |s.im|) him
        have hwT : A / Real.log T ≤ A / Real.log |s.im| :=
          div_le_div_of_nonneg_left hA.le hlt hlog
        have hw := hwidth ht
        have h := (hstrip s.re s.im ht.le (by linarith) hs.1.1.2).1
        simpa only [Complex.re_add_im] using h
      · have hδT : A / Real.log T ≤ δ := by
          apply (div_le_iff₀ hlT).mpr
          have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 3) hT
          exact hAδ.trans (mul_le_mul_of_nonneg_left hlog hδ.le)
        have hr := hcompact s (by linarith) (le_of_not_gt ht)
        intro hz
        apply hr
        rw [regularZeta_eq_mul hs1, hz, mul_zero]
    exact (differentiableAt_zeta_log_derivative hs1 hn).differentiableWithinAt

end Ostmann.Dirichlet

end OAI
