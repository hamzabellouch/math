import OAI.Geometry.CylinderCovering.Ruled.LocalEndpoint

namespace OAI

noncomputable section
open Set
namespace RuledApproximation.HyperbolicJacobian

lemma matrix_det_one_add_smul (A : Matrix (Fin 2) (Fin 2) ℝ) (s : ℝ) :
    Matrix.det (1 + s • A) = 1 + s * Matrix.trace A + s ^ 2 * Matrix.det A := by
  simp [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.add_apply,
    Matrix.smul_apply]
  ring

lemma plane_det_id_add_smul (A : Plane →ₗ[ℝ] Plane) (s : ℝ) :
    LinearMap.det (LinearMap.id + s • A) =
      1 + s * LinearMap.trace ℝ Plane A + s ^ 2 * LinearMap.det A := by
  let b := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
  rw [← LinearMap.det_toMatrix b, LinearMap.trace_eq_matrix_trace ℝ b,
    ← LinearMap.det_toMatrix b]
  simpa using matrix_det_one_add_smul (LinearMap.toMatrix b b A) s

theorem hyperbolicAt_iff {L : ℝ} (hL : 0 < L) (v : Plane → Plane) (p : Plane) :
    HyperbolicAt L v p ↔
      LinearMap.trace ℝ Plane (fderiv ℝ v p).toLinearMap = 0 ∧
      LinearMap.det (fderiv ℝ v p).toLinearMap < 0 ∧
      L * Real.sqrt (-LinearMap.det (fderiv ℝ v p).toLinearMap) < 1 := by
  constructor
  · intro h
    obtain ⟨htr, hdet⟩ := CylinderCovering.ProductLocal.hyperbolicAt_trace_det hL h
    obtain ⟨lam, hlam, hsmall, hplus, _⟩ := h
    have hl : 0 < lam := (mul_pos_iff_of_pos_left hL).mp hlam
    have heq := positive_eigenvalue_eq_sqrt (fderiv ℝ v p) htr hdet hl hplus
    exact ⟨htr, hdet, heq ▸ hsmall⟩
  · rintro ⟨htr, hdet, hsmall⟩
    obtain ⟨hp, hm⟩ := plane_hyperbolic_eigenvalues (fderiv ℝ v p).toLinearMap htr hdet
    exact ⟨_, mul_pos hL (Real.sqrt_pos.mpr (neg_pos.mpr hdet)), hsmall, hp, hm⟩

theorem deformation_det {L : ℝ} (hL : 0 < L) {v : Plane → Plane} {p : Plane}
    (h : HyperbolicAt L v p) (s : ℝ) :
    LinearMap.det (LinearMap.id + s • (fderiv ℝ v p).toLinearMap) =
      1 - s ^ 2 * (Real.sqrt (-LinearMap.det (fderiv ℝ v p).toLinearMap)) ^ 2 := by
  obtain ⟨htr, hdet, _⟩ := (hyperbolicAt_iff hL v p).mp h
  rw [plane_det_id_add_smul, htr, Real.sq_sqrt (neg_nonneg.mpr hdet.le)]
  ring

theorem fderiv_deformation_det {L : ℝ} (hL : 0 < L) {v : Plane → Plane} {p : Plane}
    (hv : DifferentiableAt ℝ v p) (h : HyperbolicAt L v p) (s : ℝ) :
    LinearMap.det (fderiv ℝ (fun q => q + s • v q) p).toLinearMap =
      1 - s ^ 2 * (Real.sqrt (-LinearMap.det (fderiv ℝ v p).toLinearMap)) ^ 2 := by
  have hd := (hasFDerivAt_id p).add (hv.hasFDerivAt.const_smul s)
  change LinearMap.det (fderiv ℝ (id + s • v) p).toLinearMap = _
  rw [hd.fderiv]
  exact deformation_det hL h s

theorem deformation_det_pos {L s : ℝ} (hL : 0 < L) {v : Plane → Plane} {p : Plane}
    (h : HyperbolicAt L v p) (hs : |s| ≤ L) :
    0 < LinearMap.det (LinearMap.id + s • (fderiv ℝ v p).toLinearMap) := by
  obtain ⟨_, hdet, hsmall⟩ := (hyperbolicAt_iff hL v p).mp h
  have hl : 0 < Real.sqrt (-LinearMap.det (fderiv ℝ v p).toLinearMap) :=
    Real.sqrt_pos.mpr (neg_pos.mpr hdet)
  have hb : |s| * Real.sqrt (-LinearMap.det (fderiv ℝ v p).toLinearMap) < 1 :=
    (mul_le_mul_of_nonneg_right hs hl.le).trans_lt hsmall
  have hn : 0 ≤ |s| * Real.sqrt (-LinearMap.det (fderiv ℝ v p).toLinearMap) :=
    mul_nonneg (abs_nonneg _) hl.le
  rw [deformation_det hL h s]
  nlinarith [sq_abs s, sq_nonneg (1 - |s| *
    Real.sqrt (-LinearMap.det (fderiv ℝ v p).toLinearMap))]

theorem deformation_det_lt_one {L s : ℝ} (hL : 0 < L) {v : Plane → Plane} {p : Plane}
    (h : HyperbolicAt L v p) (hs : s ≠ 0) :
    LinearMap.det (LinearMap.id + s • (fderiv ℝ v p).toLinearMap) < 1 := by
  obtain ⟨_, hdet, _⟩ := (hyperbolicAt_iff hL v p).mp h
  have hl : 0 < Real.sqrt (-LinearMap.det (fderiv ℝ v p).toLinearMap) :=
    Real.sqrt_pos.mpr (neg_pos.mpr hdet)
  rw [deformation_det hL h s]
  exact sub_lt_self _ (mul_pos (sq_pos_of_ne_zero hs) (sq_pos_of_pos hl))

end RuledApproximation.HyperbolicJacobian

end

end OAI
