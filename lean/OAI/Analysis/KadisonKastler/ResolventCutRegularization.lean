import OAI.Analysis.KadisonKastler.GraphLowCutBound

namespace OAI

/-! # Continuous approximations to the cut projections -/

namespace KadisonKastler

noncomputable section

def resolventCutScalar (r ε s : ℝ) : ℝ := max (r - s) 0 / (max (r - s) 0 + ε)

theorem resolventCutScalar_continuous (r : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Continuous (resolventCutScalar r ε) := by
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro s
  exact ne_of_gt (add_pos_of_nonneg_of_pos (le_max_right _ _) hε)

theorem resolventCutScalar_bounds (r s : ℝ) {ε : ℝ} (hε : 0 < ε) :
    0 ≤ resolventCutScalar r ε s ∧ resolventCutScalar r ε s ≤ 1 := by
  have hm : 0 ≤ max (r - s) 0 := le_max_right _ _
  have hd : 0 < max (r - s) 0 + ε := add_pos_of_nonneg_of_pos hm hε
  exact ⟨div_nonneg hm hd.le, (div_le_one hd).mpr (by linarith)⟩

theorem resolventCutScalar_error (r s : ℝ) {ε : ℝ} (hε : 0 < ε) :
    |(resolventCutScalar r ε s - 1) * max (r - s) 0| ≤ ε := by
  have hm : 0 ≤ max (r - s) 0 := le_max_right _ _
  have hd : 0 < max (r - s) 0 + ε := add_pos_of_nonneg_of_pos hm hε
  have he : (resolventCutScalar r ε s - 1) * max (r - s) 0 =
      -ε * resolventCutScalar r ε s := by
    unfold resolventCutScalar
    field_simp
    ring
  rw [he, abs_mul, abs_neg, abs_of_pos hε,
    abs_of_nonneg (resolventCutScalar_bounds r s hε).1]
  exact mul_le_of_le_one_right hε.le (resolventCutScalar_bounds r s hε).2

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def resolventCutRegularization (R : H →L[ℂ] H) (r ε : ℝ) : H →L[ℂ] H :=
  cfc (resolventCutScalar r ε) R

theorem resolventCutRegularization_contracts (R : H →L[ℂ] H) (r : ℝ)
    {ε : ℝ} (hε : 0 < ε) : ‖resolventCutRegularization R r ε‖ ≤ 1 := by
  apply norm_cfc_le zero_le_one
  intro s _
  rw [Real.norm_eq_abs, abs_of_nonneg (resolventCutScalar_bounds r s hε).1]
  exact (resolventCutScalar_bounds r s hε).2

theorem resolventCutRegularization_factor (R : H →L[ℂ] H) (r : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    resolventCutRegularization R r ε =
      cfc (fun s : ℝ => (max (r - s) 0 + ε)⁻¹) R * resolventCutGenerator R r := by
  have hi : Continuous (fun s : ℝ => (max (r - s) 0 + ε)⁻¹) := by
    apply Continuous.inv₀ (by fun_prop)
    intro s
    exact ne_of_gt (add_pos_of_nonneg_of_pos (le_max_right _ _) hε)
  rw [resolventCutRegularization, resolventCutGenerator,
    ← cfc_mul _ _ R hi.continuousOn (by fun_prop)]
  apply cfc_congr
  intro s _
  simp only [resolventCutScalar, div_eq_mul_inv, mul_comm]

theorem resolventCutRegularization_support (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (r : ℝ) {ε : ℝ} (hε : 0 < ε) :
    resolventCutRegularization R r ε * resolventLowerCut R r =
      resolventCutRegularization R r ε := by
  have hz : resolventCutRegularization R r ε * (1 - resolventLowerCut R r) = 0 := by
    rw [resolventCutRegularization_factor R r hε, mul_assoc,
      resolventCutGenerator_mul_complement R hR r, mul_zero]
  rw [mul_sub, mul_one, sub_eq_zero] at hz
  exact hz.symm

theorem resolventCutRegularization_error (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (r : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ‖(resolventCutRegularization R r ε - 1) * resolventCutGenerator R r‖ ≤ ε := by
  rw [resolventCutRegularization, resolventCutGenerator,
    ← cfc_const_one ℝ R hR, ← cfc_sub _ _ R
      (resolventCutScalar_continuous r hε).continuousOn continuousOn_const,
    ← cfc_mul (fun s : ℝ => resolventCutScalar r ε s - 1)
      (fun s : ℝ => max (r - s) 0) R ((resolventCutScalar_continuous r hε).continuousOn.sub
      continuousOn_const) (by fun_prop)]
  apply norm_cfc_le hε.le
  intro s _
  exact resolventCutScalar_error r s hε

end

end KadisonKastler

end OAI
