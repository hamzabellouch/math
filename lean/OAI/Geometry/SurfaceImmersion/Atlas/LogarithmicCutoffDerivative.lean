import OAI.Geometry.SurfaceImmersion.Atlas.LogarithmicCutoff

namespace OAI

/-! The logarithmic cutoff has a derivative uniformly small after
 multiplication by the distance from the collar boundary. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing

lemma logarithmicCutoff_weighted_derivative {L C : ℝ} (hL : 0 < L) (hC : 0 ≤ C)
    (hb : ∀ t, |deriv Real.smoothTransition t| ≤ C) (x : ℝ) :
    |x*deriv (logarithmicCutoff L) x| ≤ C/L := by
  by_cases hx : x = 0
  · simp only [hx,zero_mul,abs_zero]
    exact div_nonneg hC hL.le
  · have hd := ((Real.smoothTransition.contDiff : ContDiff ℝ ∞ Real.smoothTransition).differentiable
        (by simp) (-Real.log x/L)).hasDerivAt.comp x ((Real.hasDerivAt_log hx).neg.div_const L)
    change HasDerivAt (fun y => Real.smoothTransition (-Real.log y/L)) _ x at hd
    rw [(logarithmicCutoff_formula hx).deriv_eq,hd.deriv]
    have he : x*(deriv Real.smoothTransition (-Real.log x/L)*(-x⁻¹/L)) =
        -deriv Real.smoothTransition (-Real.log x/L)/L := by
      field_simp
    rw [he,abs_div,abs_neg,abs_of_pos hL]
    exact div_le_div_of_nonneg_right (hb _) hL.le

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
