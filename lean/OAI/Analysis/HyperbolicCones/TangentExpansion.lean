import OAI.Analysis.HyperbolicCones.TangentIdentity

namespace OAI

noncomputable section

open scoped Matrix.Norms.L2Operator RealInnerProductSpace Topology
open Matrix Filter Asymptotics

namespace Paper256

theorem NormalizedPencil.tangent_difference_quotient (P : NormalizedPencil)
    (v h : Vec 4) (hv : ‖v‖ = 1) (hh : inner ℝ v h = 0)
    (y : Fin 3 → ℝ) (s : ℝ) (hs : s ≠ 0) :
    choiLam (wedgeCoordinates v h) y / (1 + s ^ 2 * ‖h‖ ^ 2) =
      operatorNorm (P.leftProjection v * P.B y *
        (s⁻¹ • (P.rightProjection (tangentCurve v h s) - P.rightProjection v))) ^ 2 := by
  have hval := P.norm_identity (tangentCurve v h s) v
    (tangentCurve_unit v h hv hh s) hv y
  rw [tangentCurve_wedge, choiLam_smul_left] at hval
  change (s / Real.sqrt (1 + s ^ 2 * ‖h‖ ^ 2)) ^ 2 *
    choiLam (wedgeCoordinates v h) y = _ at hval
  rw [div_pow, Real.sq_sqrt (by positivity)] at hval
  rw [Matrix.mul_smul, Matrix.mul_sub, P.same_direction_zero v hv y, sub_zero,
    operatorNorm_smul, mul_pow, sq_abs, ← hval]
  have hd : 1 + s ^ 2 * ‖h‖ ^ 2 ≠ 0 := ne_of_gt (by positivity)
  field_simp

theorem kernel_projection_tangent_expansion (c : ℕ) (hC : 0 < c)
    (E : Sym 4 →ₗ[ℝ] Sym c) :
    ∃ (v : Vec 4) (T : Vec 4 →ₗ[ℝ] Mat c ℝ),
      ‖v‖ = 1 ∧ v 0 ≠ 0 ∧ ∀ h : Vec 4, inner ℝ v h = 0 →
        (fun s : ℝ => kernelProjection (E (1 - outerSym (tangentCurve v h s)) : Mat c ℝ) -
          kernelProjection (E (1 - outerSym v) : Mat c ℝ) - s • T h) =o[𝓝 0]
          (fun s : ℝ => s) := by
  obtain ⟨v, T, hv, hv0, ht⟩ := kernel_projection_tangent_derivative c hC E
  refine ⟨v, T, hv, hv0, ?_⟩
  intro h hh
  simpa [tangentCurve] using (ht h hh).isLittleO

end Paper256

end

end OAI
