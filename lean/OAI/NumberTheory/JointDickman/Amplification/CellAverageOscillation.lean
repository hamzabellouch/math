import OAI.NumberTheory.JointDickman.Amplification.IntervalSquareBound

namespace OAI

/-! # Complex cell averages and oscillation bounds -/

namespace JointDickman
open MeasureTheory

noncomputable def complexCellAverage (a b : ℝ) (F : ℝ → ℂ) : ℂ :=
  (∫ x in a..b, F x)/(b-a : ℝ)

theorem complexCellAverage_norm_le {a b M : ℝ} {F : ℝ → ℂ}
    (hab : a < b) (hF : ∀ x ∈ Set.Icc a b, ‖F x‖ ≤ M) :
    ‖complexCellAverage a b F‖ ≤ M := by
  rw [complexCellAverage,norm_div,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (sub_pos.mpr hab)]
  apply (div_le_iff₀ (sub_pos.mpr hab)).mpr
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (f := F) (C := M) (fun x hx =>
      hF x (Set.uIcc_of_le hab.le ▸ Set.uIoc_subset_uIcc hx))
  simpa only [abs_of_pos (sub_pos.mpr hab)] using hh

/-- No regularity of the signed mass is needed to replace a test by its
cell average; only oscillation of the test enters. -/
theorem complexCellAverage_error {a b A x : ℝ} {F : ℝ → ℂ}
    (hab : a < b) (hF : IntervalIntegrable F volume a b)
    (hosc : ∀ y ∈ Set.Icc a b, ‖F x-F y‖ ≤ A) :
    ‖F x-complexCellAverage a b F‖ ≤ A := by
  have he : F x-complexCellAverage a b F =
      (∫ y in a..b, F x-F y)/(b-a : ℝ) := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const hF,
      intervalIntegral.integral_const]
    simp only [complexCellAverage,Complex.real_smul]
    push_cast
    have habc : (b : ℂ)-(a : ℂ) ≠ 0 := by exact_mod_cast (sub_pos.mpr hab).ne'
    field_simp [habc]
  rw [he,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (sub_pos.mpr hab)]
  apply (div_le_iff₀ (sub_pos.mpr hab)).mpr
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (f := fun y => F x-F y) (C := A) (fun y hy =>
      hosc y (Set.uIcc_of_le hab.le ▸ Set.uIoc_subset_uIcc hy))
  simpa only [abs_of_pos (sub_pos.mpr hab)] using h

/-- A local Lipschitz estimate incurs at most L times the cell width. -/
theorem complexCellAverage_lipschitz_error {a b L x : ℝ} {F : ℝ → ℂ}
    (hab : a < b) (hL : 0 ≤ L) (hF : IntervalIntegrable F volume a b)
    (hx : x ∈ Set.Icc a b)
    (hLip : ∀ u ∈ Set.Icc a b, ∀ v ∈ Set.Icc a b,
      ‖F u-F v‖ ≤ L*|u-v|) :
    ‖F x-complexCellAverage a b F‖ ≤ L*(b-a) := by
  apply complexCellAverage_error hab hF
  intro y hy
  apply (hLip x hx y hy).trans
  apply mul_le_mul_of_nonneg_left _ hL
  exact abs_le.mpr ⟨by linarith [hx.1, hy.2], by linarith [hx.2,hy.1]⟩

end JointDickman

end OAI
