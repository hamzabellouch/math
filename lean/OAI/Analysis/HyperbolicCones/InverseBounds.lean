import OAI.Analysis.HyperbolicCones.ConePositive

namespace OAI

noncomputable section

open Matrix Filter
open scoped Matrix.Norms.L2Operator MatrixOrder

namespace Paper256

theorem inverse_shift_le_scalar {n : ℕ} (X : Sym n)
    (hX : (X : Mat n ℝ).PosDef) (t : ℝ) (ht : 0 < t) :
    ((X : Mat n ℝ) + t • 1)⁻¹ ≤ t⁻¹ • (1 : Mat n ℝ) := by
  rw [posDef_shift_inverse_eq_cfc X hX t ht.le]
  calc
    cfc (fun x : ℝ => (x + t)⁻¹) (X : Mat n ℝ) ≤
        cfc (fun _ : ℝ => t⁻¹) (X : Mat n ℝ) := by
      apply cfc_mono _ (X.val.finite_real_spectrum.continuousOn _)
        (X.val.finite_real_spectrum.continuousOn _)
      intro x hx
      exact inv_anti₀ ht (le_add_of_nonneg_left (posDef_real_spectrum_positive hX hx).le)
    _ = algebraMap ℝ (Mat n ℝ) t⁻¹ := cfc_const t⁻¹ (X : Mat n ℝ) X.property
    _ = t⁻¹ • (1 : Mat n ℝ) := Algebra.algebraMap_eq_smul_one _

theorem phi_inverse_shift_bounds (X : Sym 4) (hX : (X : Mat 4 ℝ).PosDef)
    (y : Fin 3 → ℝ) (t : ℝ) (ht : 0 < t) :
    0 ≤ phi y ((X : Mat 4 ℝ) + t • 1)⁻¹ ∧
      phi y ((X : Mat 4 ℝ) + t • 1)⁻¹ ≤ t⁻¹ • phi y (1 : Mat 4 ℝ) := by
  constructor
  · exact (phi_posSemidef y _ (positive_shift X hX t ht.le).inv.posSemidef).nonneg
  · have h := (phi_monotone y) (inverse_shift_le_scalar X hX t ht)
    simpa only [phi_smul] using h

theorem coneResidual_eventually_posDef (X Z : Sym 4) (y : Fin 3 → ℝ)
    (hX : (X : Mat 4 ℝ).PosDef) :
    ∀ᶠ t : ℝ in atTop, (coneResidual X Z y t : Mat 4 ℝ).PosDef := by
  filter_upwards [eventually_gt_atTop ‖(coneResidual X Z y 0 : Mat 4 ℝ)‖] with t ht
  have ht0 : 0 < t := lt_of_le_of_lt (norm_nonneg _) ht
  exact posDef_of_shift_bound (coneResidual X Z y 0) (coneResidual X Z y t) t
    (coneResidual_lower_bound X Z y t
      (posDef_inverse_sub_shift_inverse_posSemidef X hX t ht0.le)) ht

theorem coneResidual_exists_singular (X Z : Sym 4) (y : Fin 3 → ℝ)
    (hX : (X : Mat 4 ℝ).PosDef)
    (h0 : ¬ (coneResidual X Z y 0 : Mat 4 ℝ).PosSemidef) :
    ∃ t : ℝ, 0 < t ∧ (coneResidual X Z y t : Mat 4 ℝ).det = 0 := by
  by_contra! h
  apply h0
  apply posSemidef_of_nonsingular_path (coneResidual X Z y)
    (continuousOn_coneResidual X Z y hX)
    (continuousAt_coneResidual X Z y 0 (by simpa using hX))
  · intro t ht
    exact (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (h t ht))
  · exact coneResidual_exists_posDef X Z y
      (fun t ht => posDef_inverse_sub_shift_inverse_posSemidef X hX t ht)

end Paper256

end

end OAI
