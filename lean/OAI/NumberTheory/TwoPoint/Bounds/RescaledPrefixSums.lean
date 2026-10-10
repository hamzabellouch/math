import OAI.NumberTheory.TwoPoint.Bounds.RoughShiftBoundary
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Finite

namespace OAI

/-! Finite weighted assembly at the actual divisor scale `Y = X/u`.
The factor `1/u` is retained exactly, including floor cutoffs. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

lemma tendsto_nat_div_atTop (u : ℕ) (hu : 0 < u) :
    Tendsto (fun X : ℕ => X / u) atTop atTop := by
  apply tendsto_atTop.2
  intro N
  filter_upwards [eventually_ge_atTop (N * u)] with X hX
  exact (Nat.le_div_iff_mul_le hu).mpr hX

lemma prefix_norm_of_average_bound (F : ℕ → ℂ) (N : ℕ) (E : ℝ)
    (hF : ‖positivePrefix F N / (N : ℂ)‖ ≤ E) :
    ‖positivePrefix F N‖ ≤ (N : ℝ) * E := by
  by_cases hN : N = 0
  · simp [hN, positivePrefix]
  have hNp : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  rw [norm_div, Complex.norm_natCast] at hF
  have ht := (div_le_iff₀ hNp).mp hF
  nlinarith only [ht]

/-- Each profile may have its own parameter. The resulting long-average
threshold is common to the finite divisor family and all parameter choices. -/
theorem finite_rescaled_prefix_bound {ι : Type*} (U : Finset ℕ)
    (a : ℕ → ℂ) (F : ℕ → ι → ℕ → ℂ) (Valid : ℕ → ι → Prop) (E : ℝ) (hE : 0 ≤ E)
    (hU : ∀ u ∈ U, 0 < u)
    (hF : ∀ u ∈ U, ∀ᶠ Y : ℕ in atTop,
      ∀ t : ι, Valid u t → ‖positivePrefix (F u t) Y / (Y : ℂ)‖ ≤ E) :
    ∀ᶠ X : ℕ in atTop, ∀ t : ℕ → ι, (∀ u ∈ U, Valid u (t u)) →
      ‖(∑ u ∈ U, a u * positivePrefix (F u (t u)) (X / u)) / (X : ℂ)‖ ≤
        E * ∑ u ∈ U, ‖a u‖ / (u : ℝ) := by
  have hall : ∀ᶠ X : ℕ in atTop, ∀ u ∈ U,
      ∀ t : ι, Valid u t → ‖positivePrefix (F u t) (X / u) / ((X / u : ℕ) : ℂ)‖ ≤ E := by
    apply (eventually_all_finset U).mpr
    intro u hu
    exact (tendsto_nat_div_atTop u (hU u hu)).eventually (hF u hu)
  filter_upwards [hall, eventually_ge_atTop 1] with X hX hX₁
  intro t ht
  have hXp : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  rw [sum_div]
  calc
    _ ≤ ∑ u ∈ U, ‖a u * positivePrefix (F u (t u)) (X / u) / (X : ℂ)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ u ∈ U, E * (‖a u‖ / (u : ℝ)) := by
      apply sum_le_sum
      intro u hu
      have hup : (0 : ℝ) < u := by exact_mod_cast hU u hu
      have hb := prefix_norm_of_average_bound (F u (t u)) (X / u) E (hX u hu (t u) (ht u hu))
      have hratio : ((X / u : ℕ) : ℝ) ≤ (X : ℝ) / u := Nat.cast_div_le
      have hprefix : ‖positivePrefix (F u (t u)) (X / u)‖ ≤ ((X : ℝ) / u) * E :=
        hb.trans (mul_le_mul_of_nonneg_right hratio hE)
      rw [norm_div, norm_mul, Complex.norm_natCast]
      calc
        _ ≤ (‖a u‖ * (((X : ℝ) / u) * E)) / X := by gcongr
        _ = _ := by field_simp
    _ = _ := by rw [mul_sum]

end TwoPointCorrelations

end OAI
