import OAI.Geometry.RuledCovering.Main
import OAI.Geometry.CylinderCovering.Ruled.ComparisonDefinitions

namespace OAI

noncomputable section
namespace RuledApproximation

@[simp] lemma comparisonOperator_apply (p : Plane) :
    comparisonOperator p = vec2 (2 * p 1) (p 0 / 8) := by
  ext i
  fin_cases i <;> simp [comparisonOperator, vec2]
  ring

lemma comparisonOperator_eq_matrix : comparisonOperator = matrixCLM 0 2 (1 / 8) 0 := by
  ext p i
  fin_cases i <;> simp [comparisonOperator, matrixCLM, vec2]

lemma comparisonOperator_trace :
    LinearMap.trace ℝ Plane comparisonOperator.toLinearMap = 0 := by
  rw [comparisonOperator_eq_matrix, matrixCLM_trace]
  norm_num

lemma comparisonOperator_det : LinearMap.det comparisonOperator.toLinearMap = -(1 / 4) := by
  rw [comparisonOperator_eq_matrix, matrixCLM_det]
  norm_num

lemma comparisonOperator_eigenvalues (lam : ℝ) :
    Module.End.HasEigenvalue comparisonOperator.toLinearMap lam ↔
      lam = 1 / 2 ∨ lam = -(1 / 2) := by
  rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Polynomial.IsRoot,
    plane_charpoly, comparisonOperator_trace, comparisonOperator_det]
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_add, zero_mul, sub_zero]
  constructor
  · intro h
    have hf : (lam - 1 / 2) * (lam + 1 / 2) = 0 := by nlinarith
    rcases mul_eq_zero.mp hf with h | h
    · left; linarith
    · right; linarith
  · rintro (rfl | rfl) <;> norm_num

lemma comparisonOperator_norm : ‖comparisonOperator‖ = 2 := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro p
    have hp := norm_plane_sq p
    have hAp : ‖comparisonOperator p‖ ^ 2 = 4 * p 1 ^ 2 + p 0 ^ 2 / 64 := by
      rw [norm_plane_sq]
      simp only [comparisonOperator_apply, vec2_apply_zero, vec2_apply_one]
      ring
    have hs : ‖comparisonOperator p‖ ^ 2 ≤ (2 * ‖p‖) ^ 2 := by
      nlinarith [sq_nonneg (p 0)]
    nlinarith [norm_nonneg (comparisonOperator p), norm_nonneg p]
  · have hb := comparisonOperator.le_opNorm (vec2 0 1)
    have hn : ‖vec2 0 1‖ = 1 := by
      have hs := norm_plane_sq (vec2 0 1)
      simp only [vec2_apply_zero, vec2_apply_one] at hs
      nlinarith [norm_nonneg (vec2 0 1)]
    have hnA : ‖comparisonOperator (vec2 0 1)‖ = 2 := by
      have hs : ‖comparisonOperator (vec2 0 1)‖ ^ 2 = 4 := by
        rw [norm_plane_sq]
        norm_num
      nlinarith [norm_nonneg (comparisonOperator (vec2 0 1))]
    rw [hnA, hn, mul_one] at hb
    exact hb

lemma comparisonOperator_hyperbolic (p : Plane) :
    HyperbolicAt 1 comparisonOperator p := by
  refine ⟨1 / 2, by norm_num, by norm_num, ?_, ?_⟩
  · rw [comparisonOperator.fderiv]
    exact (comparisonOperator_eigenvalues _).mpr (Or.inl rfl)
  · rw [comparisonOperator.fderiv]
    exact (comparisonOperator_eigenvalues _).mpr (Or.inr rfl)

theorem spectralNormComparison_proof : SpectralNormComparisonStatement := by
  refine ⟨comparisonOperator_eigenvalues, comparisonOperator_norm,
    comparisonOperator_hyperbolic, ?_⟩
  rintro ⟨k, hk, hnorm⟩
  rw [comparisonOperator_norm] at hnorm
  linarith

theorem physicalScalingInvariance_proof : PhysicalScalingInvarianceStatement := by
  intro h hh A
  let e := transverseScaling h hh.ne'
  constructor
  · intro lam
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly,
      Module.End.hasEigenvalue_iff_isRoot_charpoly, e.charpoly_conj]
  · change (e.conj A).comp (e.conj A) = 0 ↔ A.comp A = 0
    rw [← e.conj_comp, map_eq_zero_iff _ e.conj.injective]

lemma transverseScaling_fderiv (h : ℝ) (hh : h ≠ 0) {v : Plane → Plane}
    {p : Plane} (hv : DifferentiableAt ℝ v p) :
    fderiv ℝ (fun q => transverseScaling h hh (v ((transverseScaling h hh).symm q)))
      (transverseScaling h hh p) =
      ((transverseScaling h hh).toContinuousLinearEquiv.toContinuousLinearMap.comp
        (fderiv ℝ v p)).comp
          (transverseScaling h hh).symm.toContinuousLinearEquiv.toContinuousLinearMap := by
  let e := (transverseScaling h hh).toContinuousLinearEquiv
  have hv' : HasFDerivAt v (fderiv ℝ v p) (e.symm (e p)) := by
    simpa using hv.hasFDerivAt
  exact (e.hasFDerivAt.comp (e p) (hv'.comp (e p) e.symm.hasFDerivAt)).fderiv

@[simp] lemma rescaledComparisonOperator_apply (p : Plane) :
    rescaledComparisonOperator p = vec2 (p 1 / 2) (p 0 / 2) := by
  ext i
  fin_cases i <;>
    simp [rescaledComparisonOperator, transverseScaling, comparisonOperator, vec2] <;> ring

lemma rescaledComparisonOperator_norm : ‖rescaledComparisonOperator‖ = 1 / 2 := by
  have hscale (p : Plane) : ‖rescaledComparisonOperator p‖ = (1 / 2) * ‖p‖ := by
    have hp := norm_plane_sq p
    have hAp : ‖rescaledComparisonOperator p‖ ^ 2 = (p 1 / 2) ^ 2 + (p 0 / 2) ^ 2 := by
      rw [norm_plane_sq]
      simp only [rescaledComparisonOperator_apply, vec2_apply_zero, vec2_apply_one]
    nlinarith [norm_nonneg p, norm_nonneg (rescaledComparisonOperator p)]
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro p
    exact (hscale p).le
  · have hb := rescaledComparisonOperator.le_opNorm (vec2 0 1)
    have hn : ‖vec2 0 1‖ = 1 := by
      have hs := norm_plane_sq (vec2 0 1)
      simp only [vec2_apply_zero, vec2_apply_one] at hs
      nlinarith [norm_nonneg (vec2 0 1)]
    rw [hscale, hn, mul_one, mul_one] at hb
    exact hb

theorem physicalNormChange_proof : PhysicalNormChangeStatement :=
  ⟨comparisonOperator_norm, rescaledComparisonOperator_norm⟩

end RuledApproximation

end

end OAI
