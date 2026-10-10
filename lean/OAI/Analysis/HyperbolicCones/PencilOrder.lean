import OAI.Analysis.HyperbolicCones.KernelSpectrum

namespace OAI

noncomputable section

open Set Filter Matrix
open scoped Topology Matrix.Norms.L2Operator MatrixOrder

namespace Paper256

theorem sym_neg_norm_le {n : ℕ} (X : Sym n) :
    -(‖(X : Mat n ℝ)‖) • (1 : Mat n ℝ) ≤ (X : Mat n ℝ) := by
  classical
  rcases isEmpty_or_nonempty (Fin n) with h | h
  · have := h
    exact (Subsingleton.elim _ _).le
  · have := h
    rw [← Algebra.algebraMap_eq_smul_one]
    apply (algebraMap_le_iff_le_spectrum (R := ℝ) (p := IsSelfAdjoint) X.property).mpr
    intro x hx
    have hh := spectrum.norm_le_norm_of_mem hx
    have hl := neg_abs_le x
    simpa only [Real.norm_eq_abs] using le_trans (neg_le_neg hh) hl

theorem sym_le_norm {n : ℕ} (X : Sym n) :
    (X : Mat n ℝ) ≤ ‖(X : Mat n ℝ)‖ • (1 : Mat n ℝ) := by
  classical
  rcases isEmpty_or_nonempty (Fin n) with h | h
  · have := h
    exact (Subsingleton.elim _ _).le
  · have := h
    rw [← Algebra.algebraMap_eq_smul_one]
    apply (le_algebraMap_iff_spectrum_le (R := ℝ) (p := IsSelfAdjoint) X.property).mpr
    intro x hx
    exact (le_abs_self x).trans (spectrum.norm_le_norm_of_mem hx)

theorem posDef_of_scalar_lower_bound {n : ℕ} {X : Mat n ℝ} {c : ℝ}
    (hc : 0 < c) (hX : c • (1 : Mat n ℝ) ≤ X) : X.PosDef := by
  have h := (Matrix.PosDef.one.smul hc).add_posSemidef hX
  simpa only [add_sub_cancel] using h

theorem posDef_scalar_lower_bound {n : ℕ} (X : Mat n ℝ) (hX : X.PosDef) :
    ∃ c : ℝ, 0 < c ∧ c • (1 : Mat n ℝ) ≤ X := by
  classical
  rcases isEmpty_or_nonempty (Fin n) with h | h
  · have := h
    exact ⟨1, zero_lt_one, (Subsingleton.elim _ _).le⟩
  · have := h
    have hh := (CFC.exists_pos_algebraMap_le_iff X hX.isHermitian).mpr
      (fun x hx => posDef_real_spectrum_positive hX hx)
    simpa only [Algebra.algebraMap_eq_smul_one] using hh

theorem isOpen_posDef (n : ℕ) : IsOpen {X : Sym n | (X : Mat n ℝ).PosDef} := by
  apply Metric.isOpen_iff.mpr
  intro H hH
  obtain ⟨c, hc, hbound⟩ := posDef_scalar_lower_bound (H : Mat n ℝ) hH
  refine ⟨c / 2, by positivity, ?_⟩
  intro X hX
  have hnorm : ‖((X - H : Sym n) : Mat n ℝ)‖ < c / 2 := by
    simpa only [Metric.mem_ball, dist_eq_norm, AddSubgroup.coe_norm] using hX
  have hlower : -(c / 2) • (1 : Mat n ℝ) ≤ ((X - H : Sym n) : Mat n ℝ) :=
    (smul_le_smul_of_nonneg_right (by linarith : -(c / 2) ≤ -‖((X - H : Sym n) : Mat n ℝ)‖)
      Matrix.PosSemidef.one.nonneg).trans (sym_neg_norm_le (X - H))
  apply posDef_of_scalar_lower_bound (show 0 < c / 2 by positivity)
  have hh : c • (1 : Mat n ℝ) + -(c / 2) • (1 : Mat n ℝ) ≤
      (H : Mat n ℝ) + ((X : Mat n ℝ) - (H : Mat n ℝ)) := add_le_add hbound hlower
  convert hh using 1 <;> module

end Paper256

end

end OAI
