import OAI.Analysis.CircleDomains.Transfer.ModelHeightWorkingError
import OAI.Analysis.CircleDomains.Transfer.ModelAppendedPairs
import OAI.Analysis.CircleDomains.Sobolev.CutoffEnergyAlgebra
import OAI.Analysis.CircleDomains.Topology.PlanarPairCalculus

namespace OAI

/-! Outside the actual changed horizontal support, only the vertical
error remains in the selected two-coordinate source map. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem planePair_same_first_norm (a b c : ℝ) :
    ‖planePair a b-planePair a c‖ = |b-c| := by
  have h : ‖planePair a b-planePair a c‖^2 = (b-c)^2 := by
    rw [plane_norm_sq]
    simp only [PiLp.sub_apply, planePair_zero, planePair_one, sub_self, zero_pow (by decide : 2 ≠ 0), zero_add]
  nlinarith [norm_nonneg (planePair a b-planePair a c), abs_nonneg (b-c), sq_abs (b-c)]

namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem compact_pair_error_outside_support (M : CompactScalarModel G u)
    {R d ζ δ : ℝ} (H : ControlledHeight R d) (T : ℝ → ℝ)
    (hT : ∀ t, |T t-t| ≤ ζ) (η : ℂ → ℝ) (θ : EuclideanPlane → ℝ)
    (χ : ℕ → ℂ → ℝ) (c : ℕ → ℝ)
    {x : EuclideanPlane} (hx : x ∈ physicalPlaneDomain G)
    (hη : η (complexPlaneCoordinates x) = 1)
    (hθ : θ (complexPlaneCoordinates.symm (M.function (complexPlaneCoordinates x))) = 1)
    (hH : |H.height (M.function (complexPlaneCoordinates x))-
      (M.function (complexPlaneCoordinates x)).im| ≤ δ)
    (hs : complexPlaneCoordinates x ∉ ⋃ n, support (χ n)) :
    ‖planePair (M.compactPrioritySource χ c η x) (M.compactHeightSource H T θ x)-
      planePair ((M.function (complexPlaneCoordinates x)).re) ((M.function (complexPlaneCoordinates x)).im)‖ ≤ ζ+δ := by
  have hp : M.compactPrioritySource χ c η x = (M.function (complexPlaneCoordinates x)).re := by
    simp only [compactPrioritySource, hη, one_mul]
    rw [priorityInfiniteValue_eq_outside_support χ c (fun z : ℂ => M.horizontalSection (z : Sphere)) hs]
    simpa only [planeSphere, extendAtInfinity_coe, finiteCoord_coe] using M.horizontalSection_on_domain hx
  rw [hp, planePair_same_first_norm]
  exact M.compact_height_uniform_error H T hT θ hx hθ hH

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
