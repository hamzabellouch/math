import OAI.NumberTheory.TwoPoint.Fourier.ModFivePsiDecay
import OAI.NumberTheory.TwoPoint.Fourier.ModFiveZetaPsi
import OAI.NumberTheory.TwoPoint.Fourier.ModFiveInputExtension

namespace OAI

/-! The fixed modulus-five prime number theorem follows from the three
nonprincipal contour estimates, the zeta prime number theorem, and finite
character orthogonality. -/

namespace TwoPointCorrelations

open Filter Finset
open scoped BigOperators Classical

local instance : Fact (1 < (5 : ℕ)) := ⟨by decide⟩

lemma modFive_character_card : Fintype.card (DirichletCharacter ℂ 5) = 4 := by
  have hh := modFive_character_sum 1
  simp only [Nat.cast_one, map_one, sum_const, card_univ, nsmul_eq_mul, mul_one,
    show 1 % 5 = 1 by decide, ↓reduceIte] at hh
  exact_mod_cast hh

lemma modFive_rate_mono {a b x : ℝ} (hab : a ≤ b) :
    Real.exp (-b * Real.sqrt (Real.log x)) ≤ Real.exp (-a * Real.sqrt (Real.log x)) := by
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_right (neg_le_neg hab) (Real.sqrt_nonneg _)

theorem modFive_all_character_error : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ᶠ x : ℝ in atTop, ∀ χ : DirichletCharacter ℂ 5,
      ‖modFiveTwistedPsi χ x - (if χ = 1 then (x : ℂ) else 0)‖ ≤
        C * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  obtain ⟨a, ha, hnp⟩ := modFive_nonprincipal_psi_decay
  obtain ⟨b, B, hb, hB, hpr⟩ := modFive_principal_psi_decay
  refine ⟨min a b, B + 2, lt_min ha hb, by positivity, ?_⟩
  filter_upwards [hnp, hpr, eventually_ge_atTop (1 : ℝ)] with x hnp hpr hx χ
  by_cases hχ : χ = 1
  · subst χ
    rw [ite_eq_left rfl]
    calc
      _ ≤ B * x * Real.exp (-b * Real.sqrt (Real.log x)) := hpr
      _ ≤ (B + 2) * x * Real.exp (-(min a b) * Real.sqrt (Real.log x)) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_right (by linarith : B ≤ B + 2) (by linarith)
        · exact modFive_rate_mono (min_le_right _ _)
        · exact (Real.exp_pos _).le
        · positivity
  · rw [ite_eq_right hχ, sub_zero]
    calc
      _ ≤ 2 * x * Real.exp (-a * Real.sqrt (Real.log x)) := hnp χ hχ
      _ ≤ (B + 2) * x * Real.exp (-(min a b) * Real.sqrt (Real.log x)) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_right (by linarith : 2 ≤ B + 2) (by linarith)
        · exact modFive_rate_mono (min_le_left _ _)
        · exact (Real.exp_pos _).le
        · positivity

lemma modFive_selected_psi_error {x E : ℝ}
    (h : ∀ χ : DirichletCharacter ℂ 5,
      ‖modFiveTwistedPsi χ x - (if χ = 1 then (x : ℂ) else 0)‖ ≤ E) :
    |modFivePsi true x - x / 4| ≤ E := by
  have he : (4 : ℂ) * ((modFivePsi true x - x / 4 : ℝ) : ℂ) =
      ∑ χ : DirichletCharacter ℂ 5,
        (modFiveTwistedPsi χ x - (if χ = 1 then (x : ℂ) else 0)) := by
    rw [sum_sub_distrib]
    simp only [sum_ite_eq', mem_univ, ↓reduceIte]
    rw [← modFivePsi_true_character_sum]
    push_cast
    ring
  have hn : 4 * |modFivePsi true x - x / 4| ≤ 4 * E := by
    calc
      _ = ‖(4 : ℂ) * ((modFivePsi true x - x / 4 : ℝ) : ℂ)‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        norm_num
      _ ≤ ∑ χ : DirichletCharacter ℂ 5,
          ‖modFiveTwistedPsi χ x - (if χ = 1 then (x : ℂ) else 0)‖ := by
        rw [he]
        exact norm_sum_le _ _
      _ ≤ ∑ _χ : DirichletCharacter ℂ 5, E := sum_le_sum fun χ _ => h χ
      _ = _ := by simp [modFive_character_card]
  linarith

theorem modFive_eventual_psi : ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧
    ∀ᶠ x : ℝ in atTop, ∀ one : Bool,
      |modFivePsi one x - modFiveDensity one * x| ≤
        C * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  obtain ⟨a, A, ha, hA, hchars⟩ := modFive_all_character_error
  obtain ⟨b, B, hb, hB, hzeta⟩ := modFive_zeta_psi_decay
  refine ⟨min a b, A + B, lt_min ha hb, by positivity, ?_⟩
  filter_upwards [hchars, hzeta, eventually_ge_atTop (1 : ℝ)] with x hchars hzeta hx one
  have htrue : |modFivePsi true x - (1 / 4) * x| ≤
      A * x * Real.exp (-(min a b) * Real.sqrt (Real.log x)) := by
    have hh := modFive_selected_psi_error hchars
    have he : x / 4 = (1 / 4 : ℝ) * x := by ring
    rw [he] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (modFive_rate_mono (min_le_left _ _))
      (by positivity))
  have hz : |Chebyshev.psi x - x| ≤
      B * x * Real.exp (-(min a b) * Real.sqrt (Real.log x)) :=
    hzeta.trans (mul_le_mul_of_nonneg_left (modFive_rate_mono (min_le_right _ _))
      (by positivity))
  cases one
  · have he : modFivePsi false x - (3 / 4) * x =
        (Chebyshev.psi x - x) - (modFivePsi true x - (1 / 4) * x) := by
      linear_combination modFivePsi_complement x
    change |modFivePsi false x - (3 / 4) * x| ≤ _
    rw [he]
    exact (abs_sub _ _).trans ((add_le_add hz htrue).trans_eq (by ring))
  · change |modFivePsi true x - (1 / 4) * x| ≤ _
    exact htrue.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith : A ≤ A + B) (by linarith))
      (Real.exp_pos _).le)

/-- The logarithmically weighted prime estimate in the two selected
modulus-five classes, obtained by contour integration and orthogonality. -/
theorem modFiveThetaInput : ModFiveThetaInput := by
  obtain ⟨c, C, hc, hC, h⟩ := modFive_eventual_psi
  exact modFiveThetaInput_of_eventual_psi c C hc hC h

end TwoPointCorrelations

end OAI
