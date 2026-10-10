import Mathlib

namespace OAI

namespace Ostmann.Preliminaries
open scoped BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def massEnergy (μ : α → ℝ) : ℝ := ∑ x, μ x ^ 2

noncomputable def uniformMass (S : Finset α) (x : α) : ℝ :=
  if x ∈ S then (S.card : ℝ)⁻¹ else 0

noncomputable def uniformDefect (S : Finset α) (μ : α → ℝ) : ℝ :=
  ∑ x, (μ x - uniformMass S x) ^ 2

omit [DecidableEq α] in
theorem massEnergy_nonneg (μ : α → ℝ) : 0 ≤ massEnergy μ :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem uniformDefect_nonneg (S : Finset α) (μ : α → ℝ) :
    0 ≤ uniformDefect S μ := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

omit [DecidableEq α] in
theorem sum_eq_support_sum (S : Finset α) (μ : α → ℝ)
    (hsupport : ∀ x ∉ S, μ x = 0) : ∑ x, μ x = ∑ x ∈ S, μ x := by
  exact (Finset.sum_subset (Finset.subset_univ S) (by simpa using hsupport)).symm

@[simp] theorem uniformMass_sum (S : Finset α) (hS : S.Nonempty) :
    ∑ x, uniformMass S x = 1 := by
  simp only [uniformMass]
  simp [Finset.sum_ite_mem, ne_of_gt (show (0 : ℝ) < S.card by exact_mod_cast hS.card_pos)]

theorem uniformDefect_eq_energy_sub (S : Finset α) (hS : S.Nonempty)
    (μ : α → ℝ) (hmass : ∑ x, μ x = 1) (hsupport : ∀ x ∉ S, μ x = 0) :
    uniformDefect S μ = massEnergy μ - (S.card : ℝ)⁻¹ := by
  have hcard : (S.card : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hS.card_pos
  have hsum : ∑ x ∈ S, μ x = 1 := (sum_eq_support_sum S μ hsupport).symm.trans hmass
  have hpoint : ∀ x, (μ x - uniformMass S x) ^ 2 =
      μ x ^ 2 - if x ∈ S then 2 * μ x * (S.card : ℝ)⁻¹ - ((S.card : ℝ)⁻¹)^2 else 0 := by
    intro x
    by_cases hx : x ∈ S <;> simp [uniformMass, hx]; ring
  simp only [uniformDefect, hpoint, Finset.sum_sub_distrib, massEnergy]
  congr 1
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_sub_distrib]
  simp only [← Finset.sum_mul, ← Finset.mul_sum, hsum, Finset.sum_const, nsmul_eq_mul]
  field_simp
  norm_num

theorem reciprocal_density_penalty_nonneg {σ : ℝ} (hpos : 0 < σ) (hlt : σ < 1) :
    0 ≤ σ⁻¹ + (1 - σ)⁻¹ - 4 := by
  have hother : 0 < 1 - σ := sub_pos.mpr hlt
  have hid : σ⁻¹ + (1 - σ)⁻¹ - 4 = (2 * σ - 1)^2 / (σ * (1 - σ)) := by
    field_simp
    ring
  rw [hid]
  exact div_nonneg (sq_nonneg _) (le_of_lt (mul_pos hpos hother))

omit [DecidableEq α] in
theorem complex_test_error_sq_le (a : α → ℝ) (f : α → ℂ) :
    ‖∑ x, (a x : ℂ) * f x‖ ^ 2 ≤
      (∑ x, a x ^ 2) * (∑ x, ‖f x‖ ^ 2) := by
  have ht : ‖∑ x, (a x : ℂ) * f x‖ ≤ ∑ x, |a x| * ‖f x‖ := by
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs] using
      norm_sum_le (s := Finset.univ) (f := fun x => (a x : ℂ) * f x)
  have hn : 0 ≤ ∑ x, |a x| * ‖f x‖ :=
    Finset.sum_nonneg (fun _ _ => mul_nonneg (abs_nonneg _) (norm_nonneg _))
  calc
    ‖∑ x, (a x : ℂ) * f x‖ ^ 2 ≤ (∑ x, |a x| * ‖f x‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) ht 2
    _ ≤ (∑ x, |a x| ^ 2) * (∑ x, ‖f x‖ ^ 2) :=
      Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ = _ := by simp only [sq_abs]

theorem test_error_sq_le_card_mul_defect (S : Finset α) (μ : α → ℝ)
    (f : α → ℂ) (hf : ∑ x, ‖f x‖ ^ 2 ≤ Fintype.card α) :
    ‖∑ x, ((μ x - uniformMass S x : ℝ) : ℂ) * f x‖ ^ 2 ≤
      (Fintype.card α : ℝ) * uniformDefect S μ := by
  exact (complex_test_error_sq_le (fun x => μ x - uniformMass S x) f).trans
    (by simpa only [uniformDefect, mul_comm] using
      mul_le_mul_of_nonneg_left hf (uniformDefect_nonneg S μ))

end Ostmann.Preliminaries

end OAI
