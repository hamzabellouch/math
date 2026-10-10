import OAI.Geometry.CylinderCovering.Convexity.CompactSpectralBounds

namespace OAI

noncomputable section
open Set
namespace RuledApproximation

lemma exists_unit_eigenvector (A : Plane →L[ℝ] Plane) {lam : ℝ}
    (h : Module.End.HasEigenvalue A.toLinearMap lam) :
    ∃ v : Plane, ‖v‖ = 1 ∧ Module.End.HasEigenvector A.toLinearMap lam v := by
  obtain ⟨u, hu⟩ := h.exists_hasEigenvector
  have hu0 : u ≠ 0 := hu.2
  have hn : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu0
  refine ⟨‖u‖⁻¹ • u, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      inv_mul_cancel₀ hn]
  · refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, smul_ne_zero (inv_ne_zero hn) hu0⟩
    rw [map_smul, hu.apply_eq_smul]
    module

lemma normalized_eigenframe (A : Plane →L[ℝ] Plane) {lam : ℝ} (hlam : 0 < lam)
    (hplus : Module.End.HasEigenvalue A.toLinearMap lam)
    (hminus : Module.End.HasEigenvalue A.toLinearMap (-lam)) :
    ∃ (M : Coordinates ≃L[ℝ] Plane) (v w : Plane),
      ‖v‖ = 1 ∧ ‖w‖ = 1 ∧ A v = lam • v ∧ A w = (-lam) • w ∧
      (∀ z : Coordinates, M z = z 0 • v + z 1 • w) ∧
      (∀ z : Coordinates, M.symm (A (M z)) = ![lam * z 0, -lam * z 1]) ∧
      ‖M.toContinuousLinearMap‖ ≤ 2 := by
  obtain ⟨v, hvn, hv⟩ := exists_unit_eigenvector A hplus
  obtain ⟨w, hwn, hw⟩ := exists_unit_eigenvector A hminus
  have hvals : Function.Injective (![lam, -lam] : Fin 2 → ℝ) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> linarith
  have hli : LinearIndependent ℝ (![v, w] : Fin 2 → Plane) :=
    Module.End.eigenvectors_linearIndependent' A.toLinearMap ![lam, -lam] hvals ![v, w] (by
      intro i
      fin_cases i
      · exact hv
      · exact hw)
  let B : Module.Basis (Fin 2) ℝ Plane :=
    basisOfLinearIndependentOfCardEqFinrank hli (by simp)
  let M : Coordinates ≃L[ℝ] Plane := B.equivFun.symm.toContinuousLinearEquiv
  have hM (z : Coordinates) : M z = z 0 • v + z 1 • w := by
    simp [M, B]
  have hAv : A v = lam • v := hv.apply_eq_smul
  have hAw : A w = (-lam) • w := hw.apply_eq_smul
  refine ⟨M, v, w, hvn, hwn, hAv, hAw, hM, ?_, ?_⟩
  · intro z
    apply M.injective
    rw [M.apply_symm_apply, hM, map_add, map_smul, map_smul,
      hAv, hAw, hM]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    module
  · apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro z
    rw [ContinuousLinearEquiv.coe_coe, hM]
    calc
      ‖z 0 • v + z 1 • w‖ ≤ ‖z 0 • v‖ + ‖z 1 • w‖ := norm_add_le _ _
      _ = ‖z 0‖ + ‖z 1‖ := by rw [norm_smul, norm_smul, hvn, hwn]; ring
      _ ≤ 2 * ‖z‖ := by
        have h0 := norm_le_pi_norm z (0 : Fin 2)
        have h1 := norm_le_pi_norm z (1 : Fin 2)
        linarith

lemma eigenframe_inverse_bound_of_coefficients
    (A : Plane →L[ℝ] Plane) (M : Coordinates ≃L[ℝ] Plane) (v w : Plane)
    {m B lam : ℝ} (hm : 0 < m) (hml : m ≤ lam) (hlB : lam ≤ B)
    (hAB : ‖A‖ ≤ B) (hM : ∀ z : Coordinates, M z = z 0 • v + z 1 • w)
    (hcoeff : ∀ a b : ℝ, lam * (|a| + |b|) ≤
      (‖A‖ + lam) * ‖a • v + b • w‖) :
    ‖M.symm.toContinuousLinearMap‖ ≤ 2 * B / m := by
  have hB : 0 ≤ B := (hm.le.trans hml).trans hlB
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro p
  let z : Coordinates := M.symm p
  have hz : ‖z‖ ≤ |z 0| + |z 1| := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    fin_cases i <;> simp only [Real.norm_eq_abs]
    · exact le_add_of_nonneg_right (abs_nonneg _)
    · exact le_add_of_nonneg_left (abs_nonneg _)
  have hc : lam * (|z 0| + |z 1|) ≤ (‖A‖ + lam) * ‖p‖ := by
    have h := hcoeff (z 0) (z 1)
    rw [← hM, show M z = p from M.apply_symm_apply p] at h
    exact h
  have hbound : m * ‖z‖ ≤ (2 * B) * ‖p‖ := calc
    m * ‖z‖ ≤ m * (|z 0| + |z 1|) := mul_le_mul_of_nonneg_left hz hm.le
    _ ≤ lam * (|z 0| + |z 1|) := mul_le_mul_of_nonneg_right hml (by positivity)
    _ ≤ (‖A‖ + lam) * ‖p‖ := hc
    _ ≤ (2 * B) * ‖p‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
  change ‖z‖ ≤ 2 * B / m * ‖p‖
  rw [div_mul_eq_mul_div, le_div_iff₀ hm]
  nlinarith

end RuledApproximation

end

end OAI
