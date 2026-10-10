import OAI.Analysis.HyperbolicCones.KernelTangent
import OAI.Analysis.HyperbolicCones.TangentLimit
import OAI.Analysis.HyperbolicCones.OperatorEntries
import OAI.Analysis.HyperbolicCones.NormIdentity

namespace OAI

noncomputable section

open scoped Matrix.Norms.L2Operator RealInnerProductSpace
open Matrix

namespace Paper256

theorem NormalizedPencil.tangent_identity (P : NormalizedPencil) :
    ∃ (v : Vec 4) (T : Vec 4 →ₗ[ℝ] Mat P.c ℝ),
      ‖v‖ = 1 ∧ v 0 ≠ 0 ∧ ∀ h : Vec 4, inner ℝ v h = 0 → ∀ y : Fin 3 → ℝ,
        choiLam (wedgeCoordinates v h) y =
          operatorNorm (P.leftProjection v * P.B y * T h) ^ 2 := by
  obtain ⟨v, T, hv, hv0, ht⟩ := kernel_projection_tangent_derivative P.c P.c_pos P.E
  refine ⟨v, T, hv, hv0, ?_⟩
  intro h hh y
  let M := mulLeftLinearMap (Fin P.c) ℝ (P.leftProjection v * P.B y)
  let f : ℝ → Matrix (Fin P.a) (Fin P.c) ℝ :=
    fun s => P.leftProjection v * P.B y * P.rightProjection (tangentCurve v h s)
  have hderiv : HasDerivAt f (P.leftProjection v * P.B y * T h) 0 := by
    simpa only [f, M, NormalizedPencil.rightProjection, Function.comp_apply,
      LinearMap.coe_toContinuousLinearMap', mulLeftLinearMap_apply] using!
      M.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 (ht h hh)
  have hzero : f 0 = 0 := by
    simpa [f, tangentCurve] using P.same_direction_zero v hv y
  have hval (s : ℝ) : ‖f s‖ ^ 2 =
      s ^ 2 / (1 + s ^ 2 * ‖h‖ ^ 2) * choiLam (wedgeCoordinates v h) y := by
    have he := P.norm_identity (tangentCurve v h s) v
      (tangentCurve_unit v h hv hh s) hv y
    rw [tangentCurve_wedge, choiLam_smul_left, operatorNorm_eq_norm] at he
    change (s / Real.sqrt (1 + s ^ 2 * ‖h‖ ^ 2)) ^ 2 *
      choiLam (wedgeCoordinates v h) y = ‖f s‖ ^ 2 at he
    rw [div_pow, Real.sq_sqrt (by positivity)] at he
    exact he.symm
  have hlim := norm_sq_derivative_of_quadratic_curve f
    (P.leftProjection v * P.B y * T h) (choiLam (wedgeCoordinates v h) y)
    (‖h‖ ^ 2) (sq_nonneg _) hderiv hzero hval
  simpa only [operatorNorm_eq_norm] using hlim.symm

end Paper256

end

end OAI
