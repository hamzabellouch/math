import Mathlib
import OAI.Geometry.PrescribedPotential.CircleRadialCalculus
import OAI.Geometry.PrescribedPotential.KaehlerClosedDerivatives

namespace OAI

/-! Bootstrap Calculus. -/

section

 
noncomputable section
namespace FixedBootstrapCalculus
variable {E F G H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

lemma derivative_compatibility (B : E → E →L[ℝ] F) (C : G → G →L[ℝ] H)
    (L : E →L[ℝ] G) (M : F →L[ℝ] H)
    (hB : Differentiable ℝ B) (hC : Differentiable ℝ C)
    (he : ∀ y v, C (L y) (L v) = M (B y v)) (u w v : E) :
    fderiv ℝ C (L u) (L w) (L v) = M (fderiv ℝ B u w v) := by
  have hL := ((hC (L u)).hasFDerivAt.comp u L.hasFDerivAt).clm_apply
    (hasFDerivAt_const (L v) u)
  have hR := M.hasFDerivAt.comp u
    ((hB u).hasFDerivAt.clm_apply (hasFDerivAt_const v u))
  have he' : (fun y => C (L y) (L v)) = (fun y => M (B y v)) := funext (fun y => he y v)
  simp only [Function.comp_def] at hL hR
  rw [he'] at hL
  have hh := congrArg (fun T : E →L[ℝ] H => T w) (hL.unique hR)
  simpa only [add_apply, ContinuousLinearMap.comp_apply,
    zero_apply, map_zero, zero_add, ContinuousLinearMap.flip_apply] using hh

lemma differentiated_commutator (B : E → E →L[ℝ] F)
    (L P : G →L[ℝ] E) (Q M : H →L[ℝ] F) (V N : G → H)
    (hB : Differentiable ℝ B) (hV : Differentiable ℝ V) (hN : Differentiable ℝ N)
    (he : ∀ y, B (L y) (P y) = Q (V y) + M (N y)) (u w : G) :
    B (L u) (P w) + fderiv ℝ B (L u) (L w) (P u) =
      Q (fderiv ℝ V u w) + M (fderiv ℝ N u w) := by
  have hL := ((hB (L u)).hasFDerivAt.comp u L.hasFDerivAt).clm_apply P.hasFDerivAt
  have hR := (Q.hasFDerivAt.comp u (hV u).hasFDerivAt).add
    (M.hasFDerivAt.comp u (hN u).hasFDerivAt)
  have he' : (fun y => B (L y) (P y)) = (fun y => Q (V y) + M (N y)) := funext he
  simp only [Function.comp_def] at hL hR
  rw [he'] at hL
  have hh := congrArg (fun T : G →L[ℝ] F => T w) (hL.unique hR)
  simpa only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply] using hh
lemma lowered_remainder (M : H →L[ℝ] F) (a b c : F) (r e : H)
    (h : a + b = c + M r) (hb : b = M e) : a = c + M (r-e) := by
  rw [hb] at h
  rw [map_sub]
  exact (eq_sub_iff_add_eq.mpr h).trans (by abel)

end FixedBootstrapCalculus

end
end

end OAI
