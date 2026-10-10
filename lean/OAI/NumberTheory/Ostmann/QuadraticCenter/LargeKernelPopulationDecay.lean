import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import OAI.NumberTheory.Ostmann.Quadratic.KernelDiscardBound

namespace OAI

/-! # The high-kernel population is negligible at the original endpoint scale -/

namespace Ostmann

open Filter
open scoped BigOperators Classical

theorem eventual_large_kernel_population_decay (η ε a : ℝ)
    (hη : 0 < η) (hηU : η ≤ 1 / 1000) (_hε : 0 ≤ ε) (hεη : ε ≤ η / 100)
    (ha : 0 < a) :
    ∀ᶠ L : ℝ in atTop, ∀ (S : Finset ℤ) (f : ℤ → ℤ) (root : ℤ → ℕ)
      (m : ℕ) (h : ℤ),
      0 < m → (m : ℝ) ≤ Real.exp (η * L) → h.natAbs.Coprime m →
      ((S.image f).card : ℝ) ≤ Real.exp (3 * ε * L) →
      (∀ x ∈ S, f x * (root x : ℤ) ^ 2 = (m : ℤ) * x - h) →
      (∀ x ∈ S, ∀ y ∈ S, |((x - y : ℤ) : ℝ)| ≤ Real.exp L) →
      ((S.filter fun x => Real.exp (η * L) < |(f x : ℝ)|).card : ℝ) ≤
        a * Real.exp (L / 2) / L ^ 6 := by
  obtain ⟨C, hC, hbound⟩ := exists_large_kernel_discard_bound
  have hp := ((isLittleO_pow_exp_pos_mul_atTop 6 (show 0 < η / 4 by positivity)).const_mul_left
    (2 * C / a)).bound (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [hp, eventually_ge_atTop (1 : ℝ)] with L hpoly hL S f root m h hm hmU hred hcount hroot hspan
  have hLpos : 0 < L := by linarith
  have hb := hbound S f root m h (Real.exp L) (Real.exp (η * L)) hm
    (Real.exp_nonneg _) (Real.exp_pos _) hred hroot hspan
  have hmain : Real.sqrt (Real.exp L / Real.exp (η * L)) = Real.exp ((1 - η) * L / 2) := by
    rw [← Real.exp_sub]
    have he : Real.exp (L - η * L) = (Real.exp ((1 - η) * L / 2)) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; norm_num; ring
    rw [he, Real.sqrt_sq (Real.exp_nonneg _)]
  have hmroot : Real.sqrt (m : ℝ) ≤ Real.exp (η * L / 2) := by
    have hh := Real.sqrt_le_sqrt hmU
    have he : Real.exp (η * L) = (Real.exp (η * L / 2)) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; norm_num; ring
    rwa [he, Real.sqrt_sq (Real.exp_nonneg _)] at hh
  have hfirst : Real.exp (3 * ε * L) * Real.exp ((1 - η) * L / 2) ≤
      Real.exp ((1 / 2 - η / 4) * L) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (show 0 ≤ η / 100 - ε by linarith) hLpos.le]
  have hsecond : Real.exp (3 * ε * L) * Real.exp (η * L / 2) ≤
      Real.exp ((1 / 2 - η / 4) * L) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hh : 3 * ε + η / 2 ≤ 1 / 2 - η / 4 := by linarith
    nlinarith [mul_le_mul_of_nonneg_right hh hLpos.le]
  have hdecay : 2 * C * Real.exp ((1 / 2 - η / 4) * L) ≤ a * Real.exp (L / 2) / L ^ 6 := by
    have hp' : (2 * C / a) * L ^ 6 ≤ Real.exp (η / 4 * L) := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (2 * C / a) * L ^ 6),
        abs_of_pos (Real.exp_pos _), one_mul] using hpoly
    apply (le_div_iff₀ (pow_pos hLpos 6)).mpr
    have hp'' : 2 * C * L ^ 6 ≤ a * Real.exp (η / 4 * L) := by
      have hh : (2 * C * L ^ 6) / a ≤ Real.exp (η / 4 * L) := by
        simpa only [div_mul_eq_mul_div] using hp'
      nlinarith only [(div_le_iff₀ ha).mp hh]
    have hx := mul_le_mul_of_nonneg_right hp'' (Real.exp_nonneg ((1 / 2 - η / 4) * L))
    have he : Real.exp (η / 4 * L) * Real.exp ((1 / 2 - η / 4) * L) = Real.exp (L / 2) := by
      rw [← Real.exp_add]; congr 1; ring
    calc
      _ = (2 * C * L ^ 6) * Real.exp ((1 / 2 - η / 4) * L) := by ring
      _ ≤ (a * Real.exp (η / 4 * L)) * Real.exp ((1 / 2 - η / 4) * L) := hx
      _ = _ := by rw [mul_assoc, he]
  calc
    _ ≤ (S.image f).card * (C * (Real.sqrt (Real.exp L / Real.exp (η * L)) + Real.sqrt m)) := hb
    _ ≤ Real.exp (3 * ε * L) * (C * (Real.exp ((1 - η) * L / 2) + Real.exp (η * L / 2))) := by
      rw [hmain]
      exact mul_le_mul hcount (mul_le_mul_of_nonneg_left (add_le_add le_rfl hmroot) hC.le)
        (by positivity) (by positivity)
    _ ≤ 2 * C * Real.exp ((1 / 2 - η / 4) * L) := by
      have hh₁ := mul_le_mul_of_nonneg_left hfirst hC.le
      have hh₂ := mul_le_mul_of_nonneg_left hsecond hC.le
      nlinarith only [hh₁, hh₂]
    _ ≤ _ := hdecay

end Ostmann

end OAI
