import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace OAI

/-!
# Integrating the logarithmic derivative

The calculus step in `lem:residue` of paper 031-01. After the zero
comparison bounds the logarithmic derivative of
`F(σ) = (σ-1) ζ_K(σ)`, this lemma compares `F(1+h)` with its residue
`F(1)` on an interval of length at most `4/log D`.
The analytic continuation and the zeta identities are separate inputs.
-/

open Set

namespace DukePrimeDegree

/-- Integrating a uniform bound on the logarithmic derivative gives a
multiplicative comparison of the endpoint values. -/
theorem comparison_of_log_deriv_bound
    (F : ℝ → ℝ) {a b C : ℝ} (hab : a < b)
    (ha : 0 < F a) (hb : 0 < F b)
    (hcont : ContinuousOn (fun x => Real.log (F x)) (Icc a b))
    (hdiff : DifferentiableOn ℝ (fun x => Real.log (F x)) (Ioo a b))
    (hbound : ∀ x ∈ Ioo a b, |deriv (fun y => Real.log (F y)) x| ≤ C) :
    Real.exp (-C * (b - a)) * F a ≤ F b ∧
      F b ≤ Real.exp (C * (b - a)) * F a := by
  obtain ⟨x, hx, heq⟩ := exists_deriv_eq_slope (fun x => Real.log (F x)) hab hcont hdiff
  have h := hbound x hx
  rw [heq, abs_div, abs_of_pos (sub_pos.mpr hab)] at h
  have habs := (div_le_iff₀ (sub_pos.mpr hab)).mp h
  obtain ⟨hl, hu⟩ := abs_le.mp habs
  constructor
  · calc
      Real.exp (-C * (b - a)) * F a =
          Real.exp (-C * (b - a) + Real.log (F a)) := by
        rw [Real.exp_add, Real.exp_log ha]
      _ ≤ Real.exp (Real.log (F b)) := Real.exp_le_exp.mpr (by linarith)
      _ = F b := Real.exp_log hb
  · calc
      F b = Real.exp (Real.log (F b)) := (Real.exp_log hb).symm
      _ ≤ Real.exp (C * (b - a) + Real.log (F a)) :=
        Real.exp_le_exp.mpr (by linarith)
      _ = Real.exp (C * (b - a)) * F a := by
        rw [Real.exp_add, Real.exp_log ha]

/-- The uniform form used at `h ≤ 4/log D`. The comparison constant
is independent of `L` and of `h`, including arbitrarily small `h`. -/
theorem residue_comparison_on_short_interval
    (F : ℝ → ℝ) {L h C : ℝ} (hL : 0 < L) (hh : 0 < h)
    (hC : 0 ≤ C) (hlength : h ≤ 4 / L)
    (hresidue : 0 < F 1) (hvalue : 0 < F (1 + h))
    (hcont : ContinuousOn (fun x => Real.log (F x)) (Icc 1 (1 + h)))
    (hdiff : DifferentiableOn ℝ (fun x => Real.log (F x)) (Ioo 1 (1 + h)))
    (hbound : ∀ x ∈ Ioo 1 (1 + h), |deriv (fun y => Real.log (F y)) x| ≤ C * L) :
    Real.exp (-4 * C) * F 1 ≤ F (1 + h) ∧
      F (1 + h) ≤ Real.exp (4 * C) * F 1 := by
  have hab : (1 : ℝ) < 1 + h := by linarith
  obtain ⟨hl, hu⟩ := comparison_of_log_deriv_bound F hab hresidue hvalue hcont hdiff hbound
  have hlen : h * L ≤ 4 := (le_div_iff₀ hL).mp hlength
  have hprod : C * L * (1 + h - 1) ≤ 4 * C := by
    nlinarith [mul_le_mul_of_nonneg_left hlen hC]
  constructor
  · apply le_trans _ hl
    apply mul_le_mul_of_nonneg_right _ hresidue.le
    apply Real.exp_le_exp.mpr
    linarith
  · apply hu.trans
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hprod) hresidue.le

/-- The elementary estimate after applying the real Hadamard identity.
Here `S` is the nonnegative zero sum and `G` is the gamma-factor term. -/
lemma log_derivative_bound_from_hadamard
    {L σ A B S G d : ℝ} (hL : 1 ≤ L) (hσ : 1 ≤ σ)
    (hB : 0 ≤ B) (hS : 0 ≤ S) (hSup : S ≤ A * L)
    (hG : |G| ≤ B) (hd : d = S - 1 / σ - L / 2 - G) :
    |d| ≤ (A + B + 2) * L := by
  have hσpos : 0 < σ := zero_lt_one.trans_le hσ
  have hinv : 0 ≤ 1 / σ := div_nonneg zero_le_one hσpos.le
  have hinv' : 1 / σ ≤ 1 := (div_le_iff₀ hσpos).mpr (by linarith)
  obtain ⟨hGlow, hGup⟩ := abs_le.mp hG
  rw [hd]
  apply abs_le.mpr
  constructor <;> nlinarith

/-- Evaluating at `h = 1/L` and using `ζ(1+h) ≥ 1` bounds the reciprocal
residue. `hupper` is the upper endpoint comparison just proved. -/
lemma reciprocal_residue_bound {κ F L C : ℝ}
    (hκ : 0 < κ) (hL : 0 < L)
    (hvalue : 1 / L ≤ F) (hupper : F ≤ Real.exp (4 * C) * κ) :
    1 / κ ≤ Real.exp (4 * C) * L := by
  have hprod : 1 ≤ (Real.exp (4 * C) * κ) * L :=
    (div_le_iff₀ hL).mp (hvalue.trans hupper)
  apply (div_le_iff₀ hκ).mpr
  nlinarith

end DukePrimeDegree

end OAI
