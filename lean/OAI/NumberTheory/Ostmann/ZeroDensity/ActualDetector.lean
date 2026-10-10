import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import OAI.NumberTheory.Ostmann.Dirichlet.Tail
import OAI.NumberTheory.Ostmann.ZeroDensity.DetectorLength

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace Ostmann.ZeroDensity

theorem twistedPolynomial_zeta {q : ℕ} (χ : DirichletCharacter ℂ q) (N : ℕ) (s : ℂ) :
    twistedPolynomial χ (ζ : ArithmeticFunction ℂ) N s =
      Ostmann.Dirichlet.dirichletPolynomial χ N s := by
  unfold twistedPolynomial Ostmann.Dirichlet.dirichletPolynomial
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
  simp [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply_ne hn0]

theorem actual_zero_mollified_product_le {q Q H X : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hqQ : q ≤ Q)
    (hH : 1 ≤ H) (hX : 1 ≤ X) {ρ : ℂ} (hzero : χ.LFunction ρ = 0)
    (hβ : 1 / 2 ≤ ρ.re) (hβ1 : ρ.re ≤ 1) (hheight : |ρ.im| ≤ H) :
    ‖twistedPolynomial χ (μ : ArithmeticFunction ℂ) X ρ *
      twistedPolynomial χ (ζ : ArithmeticFunction ℂ) (detectorLength Q H X) ρ‖ ≤ 5 / 16 := by
  have hq : 1 ≤ q := NeZero.pos q
  have hQ : 1 ≤ Q := hq.trans hqQ
  have hN : 1 ≤ detectorLength Q H X := hX.trans (detectorLength_ge hQ hH hX)
  have hβpos : 0 < ρ.re := by linarith
  have hHR : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hqQR : (q : ℝ) ≤ Q := by exact_mod_cast hqQ
  have hnorm : ‖ρ‖ ≤ 2 * H := by
    calc
      ‖ρ‖ ≤ |ρ.re| + |ρ.im| := Complex.norm_le_abs_re_add_abs_im ρ
      _ ≤ 1 + H := by rw [abs_of_pos hβpos]; linarith
      _ ≤ 2 * H := by linarith
  have hratio : ‖ρ‖ / ρ.re ≤ 4 * H := by
    apply (div_le_iff₀ hβpos).mpr
    nlinarith
  have hprefactor : (q : ℝ) * (1 + ‖ρ‖ / ρ.re) ≤ 5 * Q * H := by
    calc
      (q : ℝ) * (1 + ‖ρ‖ / ρ.re) ≤ (Q : ℝ) * (5 * H) := by
        apply mul_le_mul hqQR (by linarith) (by positivity) (by positivity)
      _ = _ := by ring
  have htail := Ostmann.Dirichlet.norm_LFunction_sub_dirichletPolynomial_le χ hχ hβpos hN
  rw [hzero, zero_sub, norm_neg] at htail
  have hM := norm_mollifierPolynomial_le χ X hβpos.le
  have hpow := detectorLength_rpow_le hQ hH hX hβ
  rw [norm_mul, twistedPolynomial_zeta]
  calc
    ‖twistedPolynomial χ (μ : ArithmeticFunction ℂ) X ρ‖ *
        ‖Ostmann.Dirichlet.dirichletPolynomial χ (detectorLength Q H X) ρ‖ ≤
      (X : ℝ) * ((q : ℝ) * (1 + ‖ρ‖ / ρ.re) *
        (detectorLength Q H X : ℝ) ^ (-ρ.re)) := by
      exact mul_le_mul hM htail (norm_nonneg _) (Nat.cast_nonneg _)
    _ ≤ (X : ℝ) * ((5 * Q * H) * (16 * (Q : ℝ) * H * X)⁻¹) := by
      gcongr
    _ = 5 / 16 := by
      have hQ0 : (Q : ℝ) ≠ 0 := by positivity
      have hH0 : (H : ℝ) ≠ 0 := by positivity
      have hX0 : (X : ℝ) ≠ 0 := by positivity
      field_simp

theorem actual_zero_detector {q Q H X : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hqQ : q ≤ Q)
    (hH : 1 ≤ H) (hX : 1 ≤ X) {ρ : ℂ} (hzero : χ.LFunction ρ = 0)
    (hβ : 1 / 2 ≤ ρ.re) (hβ1 : ρ.re ≤ 1) (hheight : |ρ.im| ≤ H) :
    1 / 2 ≤ ‖detectorPolynomial χ X (detectorLength Q H X) ρ‖ := by
  have hQ : 1 ≤ Q := by have := NeZero.pos q; omega
  apply detector_large_of_small_product χ hX (detectorLength_ge hQ hH hX) ρ
  have h := actual_zero_mollified_product_le χ hχ hqQ hH hX hzero hβ hβ1 hheight
  linarith

end Ostmann.ZeroDensity

end

end OAI
