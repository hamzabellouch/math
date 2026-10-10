import OAI.Geometry.RuledCovering.Main
import OAI.Geometry.CylinderCovering.Ruled.ZeroDiagonalDefinitions

namespace OAI

noncomputable section
open Set
namespace RuledApproximation

lemma inner_vec2_left (x y : ℝ) (z : Plane) :
    inner ℝ (vec2 x y) z = x * z 0 + y * z 1 := by
  nth_rw 1 [← vec2_coordinates z]
  simp [vec2, EuclideanSpace.inner_toLp_toLp, dotProduct, Fin.sum_univ_succ]
  ring

lemma plane_trace_coordinates (A : Plane →L[ℝ] Plane) :
    LinearMap.trace ℝ Plane A.toLinearMap =
      A (vec2 1 0) 0 + A (vec2 0 1) 1 := by
  have h0 : (EuclideanSpace.single 0 1 : Plane) = vec2 1 0 := by
    ext i; fin_cases i <;> simp [vec2]
  have h1 : (EuclideanSpace.single 1 1 : Plane) = vec2 0 1 := by
    ext i; fin_cases i <;> simp [vec2]
  rw [LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis,
    Matrix.trace_fin_two]
  simp [LinearMap.toMatrix_apply, EuclideanSpace.basisFun_apply,
    EuclideanSpace.basisFun_repr, h0, h1]

lemma trace_zero_unit_isotropic (A : Plane →L[ℝ] Plane)
    (htr : LinearMap.trace ℝ Plane A.toLinearMap = 0) :
    ∃ u : Plane, ‖u‖ = 1 ∧ inner ℝ u (A u) = 0 := by
  let p : ℝ → Plane := fun t => vec2 (1 - t) t
  let q : ℝ → ℝ := fun t => inner ℝ (p t) (A (p t))
  have hq : Continuous q := by dsimp [q, p, vec2]; fun_prop
  have hsum : q 0 + q 1 = 0 := by
    rw [plane_trace_coordinates] at htr
    simpa [q, p, inner_vec2_left] using htr
  have hex : ∃ t ∈ Icc (0 : ℝ) 1, q t = 0 := by
    by_cases hzero : q 0 ≤ 0
    · exact intermediate_value_Icc (by norm_num) hq.continuousOn
        ⟨hzero, by linarith⟩
    · exact intermediate_value_Icc' (by norm_num) hq.continuousOn
        ⟨by linarith, by linarith⟩
  obtain ⟨t, ht, hqt⟩ := hex
  have hne : p t ≠ 0 := by
    intro hp
    have h0 := congrArg (fun z : Plane => z 0) hp
    have h1 := congrArg (fun z : Plane => z 1) hp
    simp [p] at h0 h1
    linarith
  refine ⟨‖p t‖⁻¹ • p t, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hne)]
  · rw [map_smul, inner_smul_right, real_inner_smul_left]
    change ‖p t‖⁻¹ * (‖p t‖⁻¹ * q t) = 0
    rw [hqt]
    ring

theorem orthogonalZeroDiagonal_proof : OrthogonalZeroDiagonalStatement := by
  intro A htr hdet
  classical
  obtain ⟨u, hu, hAu⟩ := trace_zero_unit_isotropic A htr
  have hon : Orthonormal ℝ (({0} : Set (Fin 2)).domRestrict (fun _ => u)) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hi : i = ⟨0, by simp⟩ := Subtype.ext (mem_singleton_iff.mp i.property)
    have hj : j = ⟨0, by simp⟩ := Subtype.ext (mem_singleton_iff.mp j.property)
    subst i
    subst j
    simp [hu]
  obtain ⟨B, hB⟩ := hon.exists_orthonormalBasis_extension_of_card_eq (by simp)
  have hB0 : B 0 = u := hB 0 (by simp)
  let R : Plane ≃ₗᵢ[ℝ] Plane := B.repr.symm
  let W : Plane →L[ℝ] Plane :=
    (B.repr.toContinuousLinearMap.comp A).comp B.repr.symm.toContinuousLinearMap
  have hWconj : W.toLinearMap = B.repr.toLinearEquiv.conj A.toLinearMap := rfl
  have he0 : vec2 1 0 = EuclideanSpace.single 0 1 := by
    ext i; fin_cases i <;> simp [vec2]
  have he1 : vec2 0 1 = EuclideanSpace.single 1 1 := by
    ext i; fin_cases i <;> simp [vec2]
  have hW00 : W (vec2 1 0) 0 = 0 := by
    change B.repr (A (B.repr.symm (vec2 1 0))) 0 = 0
    rw [he0, B.repr_symm_single, B.repr_apply_apply, hB0]
    exact hAu
  have hWtrace : LinearMap.trace ℝ Plane W.toLinearMap = 0 := by
    rw [hWconj, LinearMap.trace_conj']
    exact htr
  have hW11 : W (vec2 0 1) 1 = 0 := by
    rw [plane_trace_coordinates, hW00, zero_add] at hWtrace
    exact hWtrace
  have hexp (z : Plane) : z = z 0 • vec2 1 0 + z 1 • vec2 0 1 := by
    ext i; fin_cases i <;> simp [vec2]
  have hWexp (z : Plane) :
      W z = vec2 (W (vec2 0 1) 0 * z 1) (W (vec2 1 0) 1 * z 0) := by
    nth_rw 1 [hexp z]
    rw [map_add, map_smul, map_smul]
    ext i
    fin_cases i <;> simp [hW00, hW11, mul_comm]
  have hWmat : W = matrixCLM 0 (W (vec2 0 1) 0) (W (vec2 1 0) 1) 0 := by
    ext z i
    rw [hWexp]
    simp
  have hWdet : LinearMap.det W.toLinearMap = LinearMap.det A.toLinearMap := by
    rw [hWconj]
    simpa only [LinearEquiv.conj_apply, LinearMap.comp_assoc] using
      (LinearMap.det_conj A.toLinearMap B.repr.toLinearEquiv)
  have hprod : W (vec2 0 1) 0 * W (vec2 1 0) 1 = -LinearMap.det A.toLinearMap := by
    rw [hWmat, matrixCLM_det] at hWdet
    linarith
  have hnorm (z : Plane) : ‖W z‖ ≤ ‖A‖ * ‖z‖ := by
    change ‖B.repr (A (B.repr.symm z))‖ ≤ _
    rw [B.repr.norm_map]
    exact (A.le_opNorm _).trans_eq (by rw [B.repr.symm.norm_map])
  refine ⟨R, W (vec2 0 1) 0, W (vec2 1 0) 1, hWexp, hprod,
    by linarith, ?_, ?_⟩
  · have hb := (plane_coordinate_le (W (vec2 0 1)) 0).trans (hnorm (vec2 0 1))
    simpa [vec2, EuclideanSpace.norm_eq] using hb
  · have hc := (plane_coordinate_le (W (vec2 1 0)) 1).trans (hnorm (vec2 1 0))
    simpa [vec2, EuclideanSpace.norm_eq] using hc

end RuledApproximation

end

end OAI
