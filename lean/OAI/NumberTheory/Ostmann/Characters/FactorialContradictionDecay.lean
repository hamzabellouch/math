import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import OAI.NumberTheory.Ostmann.Characters.FactorialContradictionBounds

namespace OAI

noncomputable section
open Filter
open scoped Topology
namespace Ostmann.Characters

def factorialBulk (z L : ℝ) : ℕ := ⌊z * L⌋₊

theorem factorialBulk_le {z L : ℝ} (hz : 0 ≤ z) (hL : 0 ≤ L) :
    (factorialBulk z L : ℝ) ≤ z * L := Nat.floor_le (mul_nonneg hz hL)

theorem factorialBulk_tendsto {z : ℝ} (hz : 0 < z) :
    Tendsto (fun L : ℝ => (factorialBulk z L : ℝ)) atTop atTop := by
  have h : Tendsto (fun L : ℝ => z * L - 1) atTop atTop := by
    simpa only [id_eq, sub_eq_add_neg] using
      (tendsto_id.const_mul_atTop hz).atTop_add (tendsto_const_nhds (x := -(1 : ℝ)))
  apply tendsto_atTop_mono' atTop _ h
  exact Eventually.of_forall fun L => by
    have := Nat.lt_floor_add_one (z * L)
    unfold factorialBulk
    linarith

theorem factorialMass_tendsto (n : ℕ) {z : ℝ} (hz : 0 < z) :
    Tendsto (fun L : ℝ => factorialMass n (factorialBulk z L)) atTop atTop :=
  (factorialBulk_tendsto hz).const_mul_atTop (by positivity)

theorem factorial_exponent_tendsto_atBot (A : ℝ) {z c α : ℝ}
    (hz : 0 < z) (hc : 0 < c) (hα : 0 < α) :
    Tendsto (fun L : ℝ => A * (factorialBulk z L : ℝ) - c * Real.exp (α * L))
      atTop atBot := by
  have hexp : Tendsto (fun L : ℝ => Real.exp (α * L) / L) atTop atTop := by
    simpa using tendsto_exp_mul_div_rpow_atTop 1 α hα
  have he := hexp.eventually (eventually_ge_atTop ((|A| * z + 1) / c))
  apply tendsto_atBot_mono' atTop _ tendsto_neg_atTop_atBot
  filter_upwards [he, eventually_ge_atTop (1 : ℝ)] with L hE hL
  have hLpos : 0 < L := by linarith
  have hEmul := (le_div_iff₀ hLpos).mp hE
  have hEc := mul_le_mul_of_nonneg_left hEmul hc.le
  have hcancel : c * (((|A| * z + 1) / c) * L) = (|A| * z + 1) * L := by
    field_simp
  rw [hcancel] at hEc
  have hbulk : A * (factorialBulk z L : ℝ) ≤ |A| * (z * L) := by
    calc
      _ ≤ |A| * (factorialBulk z L : ℝ) :=
        mul_le_mul_of_nonneg_right (le_abs_self A) (Nat.cast_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left (factorialBulk_le hz.le hLpos.le) (abs_nonneg A)
  nlinarith

theorem factorial_error_tendsto_zero (n : ℕ) (A : ℝ) {z c α : ℝ}
    (hz : 0 < z) (hc : 0 < c) (hα : 0 < α) :
    Tendsto (fun L : ℝ =>
      Real.exp (A * factorialMass n (factorialBulk z L) - c * Real.exp (α * L)))
      atTop (𝓝 0) := by
  simpa only [factorialMass, mul_assoc, Function.comp_def] using
    Real.tendsto_exp_atBot.comp
      (factorial_exponent_tendsto_atBot (A * (2 : ℝ)^(n+1)) hz hc hα)

end Ostmann.Characters

end

end OAI
