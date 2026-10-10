import OAI.Geometry.RCD.Sobolev.InteriorSmoothTestBounds

namespace OAI

/-! # Directional derivatives retain the original compact smooth-test domain -/

open Set
open scoped ContDiff
noncomputable section
namespace RegularPointCoordinates

theorem InteriorSmoothTest.fderiv_apply {n : ℕ} {S : ℝ} {ψ : Euclidean n → ℝ}
    (hψ : InteriorSmoothTest n S ψ) (v : Euclidean n) :
    InteriorSmoothTest n S (fun x => fderiv ℝ ψ x v) := by
  refine ⟨?_,hψ.2.1.fderiv_apply ℝ v,(tsupport_fderiv_apply_subset ℝ v).trans hψ.2.2⟩
  exact (hψ.1.fderiv_right (by simp)).clm_apply contDiff_const

end RegularPointCoordinates

end

end OAI
