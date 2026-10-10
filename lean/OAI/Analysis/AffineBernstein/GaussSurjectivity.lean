import Mathlib
import OAI.Analysis.AffineBernstein.GaussCoordinates

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section GaussSurjectivity
open Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The gradient of a convex defining function at a zero level point is an
outward supporting covector, and cannot vanish when a strict sublevel point exists. -/
lemma convex_sublevel_gradient_support {W : Set E} {F : E → ℝ}
    (hcv : ConvexOn ℝ W F) {y z : E} (hy : y ∈ W) (hz : z ∈ W)
    (hyF : F y = 0) (hzF : F z < 0) (hd : DifferentiableAt ℝ F y) :
    gradient F y ≠ 0 ∧ IsMaxOn (fun x => inner ℝ (gradient F y) x)
      {x | x ∈ W ∧ F x ≤ 0} y := by
  have hgrad (x : E) : inner ℝ (gradient F y) x = fderiv ℝ F y x := by
    simp [gradient, InnerProductSpace.toDual_symm_apply]
  constructor
  · intro he
    have hh := convex_first_order hcv hy hz hd
    have hz' := hgrad (z-y)
    rw [he,inner_zero_left] at hz'
    rw [← hz',hyF] at hh
    linarith
  · intro x hx
    have hh := convex_first_order hcv hy hx.1 hd
    rw [← hgrad,inner_sub_right,hyF] at hh
    change inner ℝ (gradient F y) x ≤ inner ℝ (gradient F y) y
    linarith [hx.2]

/-- Every zero-level boundary point is the true support gradient in its
nonzero outward gradient direction; no parametrization surjectivity is assumed. -/
lemma gaussPoint_convex_sublevel {W : Set E} {F : E → ℝ}
    (hcv : ConvexOn ℝ W F) {y z : E} (hy : y ∈ W) (hz : z ∈ W)
    (hyF : F y = 0) (hzF : F z < 0) (hd : DifferentiableAt ℝ F y)
    (hK : IsCompact {x | x ∈ W ∧ F x ≤ 0})
    (hh : DifferentiableAt ℝ (homogeneousSupport {x | x ∈ W ∧ F x ≤ 0})
      (gradient F y)) :
    gaussPoint {x | x ∈ W ∧ F x ≤ 0} (gradient F y) = y := by
  exact gaussPoint_eq_of_max hK ⟨hy,hyF.le⟩
    (homogeneousSupport_eq_of_max ⟨hy,hyF.le⟩
      (convex_sublevel_gradient_support hcv hy hz hyF hzF hd).2) hh

end GaussSurjectivity


end
end AffineBernstein
end

end OAI
