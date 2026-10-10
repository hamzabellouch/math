import OAI.Analysis.NumericalRange.Main

namespace OAI

/-! Intrinsic domains, optimal similarities and matrix-valued boundary representations. -/

section
noncomputable section
open Set Filter Metric Complex MeasureTheory
open scoped Matrix Topology ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
namespace CompleteCrouzeix
namespace AdmissibleDomain
variable (D : AdmissibleDomain)
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

theorem positiveDensity_analytic_bound_unit
    {n m : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    [Fintype m] [DecidableEq m]
    (A : Matrix n n ℂ) (hA : spectrum ℂ A ⊆ D.domain)
    (hc : (matrixAnalyticEval A D.interior.toDisk)ᴴ *
      matrixAnalyticEval A D.interior.toDisk ≤ 1)
    (v : ℂ → Matrix m m ℂ) (hv : AnalyticOnNhd ℂ v (closure D.domain))
    (hb : ∀ z ∈ closure D.domain, ‖v z‖ ≤ 1) :
    ‖completeAnalyticEval A v‖ ≤ 1 := by
  rw [D.positiveDensity_representation A hA hv]
  apply norm_integral_density_kron
  · exact (D.positiveDensity A hA).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact (continuous_kron (D.positiveDensity A hA).continuous
      (D.trace v hv).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · intro t
    exact Matrix.nonneg_iff_posSemidef.mp (D.positiveDensity_nonneg A hA hc t)
  · exact D.positiveDensity_mass A hA
  · intro t
    exact hb _ (frontier_subset_closure (D.G_boundary t.toCircle.property))

theorem positiveDensity_analytic_bound
    {n m : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    [Fintype m] [DecidableEq m]
    (A : Matrix n n ℂ) (hA : spectrum ℂ A ⊆ D.domain)
    (hc : (matrixAnalyticEval A D.interior.toDisk)ᴴ *
      matrixAnalyticEval A D.interior.toDisk ≤ 1)
    (v : ℂ → Matrix m m ℂ) (hv : AnalyticOnNhd ℂ v (closure D.domain))
    {b : ℝ} (hb : 0 ≤ b) (hbound : ∀ z ∈ closure D.domain, ‖v z‖ ≤ b) :
    ‖completeAnalyticEval A v‖ ≤ b := by
  by_cases hb0 : b = 0
  · subst b
    rw [D.positiveDensity_representation A hA hv]
    have hz (t : UnitAddCircle) : D.trace v hv t = 0 :=
      norm_eq_zero.mp (le_antisymm
        (hbound _ (frontier_subset_closure (D.G_boundary t.toCircle.property))) (norm_nonneg _))
    simp only [hz, Matrix.kronecker_zero, integral_zero, norm_zero, le_refl]
  · have hbp : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
    let L := D.positiveDensity A hA
    let F : C(UnitAddCircle, Matrix m m ℂ) := (b⁻¹ : ℝ) • D.trace v hv
    have hn : ‖∫ t, L t ⊗ₖ F t ∂AddCircle.haarAddCircle‖ ≤ 1 := by
      apply norm_integral_density_kron
      · exact L.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      · exact (continuous_kron L.continuous F.continuous).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      · intro t
        exact Matrix.nonneg_iff_posSemidef.mp (D.positiveDensity_nonneg A hA hc t)
      · exact D.positiveDensity_mass A hA
      · intro t
        change ‖(b⁻¹ : ℝ) • D.trace v hv t‖ ≤ 1
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hbp)]
        calc
          _ ≤ b⁻¹ * b := mul_le_mul_of_nonneg_left
            (hbound _ (frontier_subset_closure (D.G_boundary t.toCircle.property))) (inv_nonneg.mpr hb)
          _ = 1 := inv_mul_cancel₀ hb0
    have he : (∫ t, L t ⊗ₖ F t ∂AddCircle.haarAddCircle) =
        (b⁻¹ : ℝ) • completeAnalyticEval A v := by
      change (∫ t, L t ⊗ₖ ((b⁻¹ : ℝ) • D.trace v hv t) ∂AddCircle.haarAddCircle) = _
      simp_rw [Matrix.kronecker_smul]
      rw [integral_smul, ← D.positiveDensity_representation A hA hv]
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hbp)] at hn
    have hh := mul_le_mul_of_nonneg_left hn hb
    simpa only [← mul_assoc, mul_inv_cancel₀ hb0, one_mul, mul_one] using hh

theorem complete_analytic_similarity_bound_nonneg
    {n m : Type*} [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m]
    {S A : Matrix n n ℂ} (hS : IsUnit S)
    (F : ℂ → Matrix m m ℂ) {b : ℝ} (hb : 0 ≤ b)
    (hF : ‖completeAnalyticEval (S*A*S⁻¹) F‖ ≤ b) :
    ‖completeAnalyticEval A F‖ ≤ (‖S‖ * ‖S⁻¹‖) * b := by
  let R := baseMatrixHom (m := m) S
  let R' := baseMatrixHom (m := m) S⁻¹
  have hi : S⁻¹*S=1 := Matrix.nonsing_inv_mul S ((Matrix.isUnit_iff_isUnit_det S).mp hS)
  have hR : R'*R=1 := by
    change baseMatrixHom (m := m) S⁻¹ * baseMatrixHom S=1
    rw [← map_mul, hi, map_one]
  have he : completeAnalyticEval A F = R'*completeAnalyticEval (S*A*S⁻¹) F*R := by
    rw [completeAnalyticEval_similarity hS]
    change completeAnalyticEval A F = R'*(R*completeAnalyticEval A F*R')*R
    calc
      _ = 1*completeAnalyticEval A F*1 := by simp
      _ = _ := by rw [← hR]; noncomm_ring
  rw [he]
  calc
    _ ≤ ‖R'‖ * ‖completeAnalyticEval (S*A*S⁻¹) F‖ * ‖R‖ :=
      (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ ‖S⁻¹‖ * b * ‖S‖ := mul_le_mul
      (mul_le_mul (baseMatrixHom_norm S⁻¹) hF (norm_nonneg _) (norm_nonneg _))
      (baseMatrixHom_norm S) (norm_nonneg _) (mul_nonneg (norm_nonneg _) hb)
    _ = _ := by ring

theorem common_positiveDensity_for_metric
    {n : ℕ} [Nonempty (Fin n)]
    (A H : Matrix (Fin n) (Fin n) ℂ) {τ : ℝ}
    (hW : numericalRange A ⊆ D.domain)
    (hf : MetricFeasible (matrixAnalyticEval A D.interior.toDisk) τ H) :
    ∃ Λ : C(UnitAddCircle, Matrix (Fin n) (Fin n) ℂ),
      (∀ t, 0 ≤ Λ t) ∧
      (∫ t, Λ t ∂AddCircle.haarAddCircle) = 1 ∧
      ∀ (m : ℕ) (v : ℂ → Matrix (Fin m) (Fin m) ℂ)
        (_ : AnalyticOnNhd ℂ v (closure D.domain)),
        completeAnalyticEval (CFC.sqrt H * A * (CFC.sqrt H)⁻¹) v =
          ∫ t, Λ t ⊗ₖ v (D.G t.toCircle) ∂AddCircle.haarAddCircle ∧
        (∀ (b : ℝ), 0 ≤ b → (∀ z ∈ closure D.domain, ‖v z‖ ≤ b) →
          ‖completeAnalyticEval A v‖ ≤ (‖CFC.sqrt H‖ * ‖(CFC.sqrt H)⁻¹‖) * b) := by
  have hp : H.PosDef := by
    have hh := Matrix.PosDef.one.add_posSemidef (hf.1 : (H - 1).PosSemidef)
    simpa only [add_sub_cancel] using hh
  let S := CFC.sqrt H
  have hu : IsUnit S := metric_sqrt_isUnit hp
  have hA : spectrum ℂ A ⊆ D.domain := (spectrum_subset_numericalRange A).trans hW
  have hA' : spectrum ℂ (S * A * S⁻¹) ⊆ D.domain := by
    rwa [spectrum_matrix_similarity hu]
  have hc : (matrixAnalyticEval (S * A * S⁻¹) D.interior.toDisk)ᴴ *
      matrixAnalyticEval (S * A * S⁻¹) D.interior.toDisk ≤ 1 := by
    rw [matrixAnalyticEval_similarity hu]
    exact (matrix_contractivity_iff _).mpr (metric_similarity_contraction hf hp)
  refine ⟨D.positiveDensity (S * A * S⁻¹) hA',
    D.positiveDensity_nonneg _ hA' hc, D.positiveDensity_mass _ hA', ?_⟩
  intro m v hv
  constructor
  · exact D.positiveDensity_representation _ hA' hv
  · intro b hb hbound
    exact complete_analytic_similarity_bound_nonneg hu v hb
      (D.positiveDensity_analytic_bound _ hA' hc v hv hb hbound)

end AdmissibleDomain
end CompleteCrouzeix
end
end

end OAI
