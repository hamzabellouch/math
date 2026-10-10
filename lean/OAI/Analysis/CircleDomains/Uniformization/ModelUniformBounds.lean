import OAI.Analysis.CircleDomains.Sobolev.ModelLocalEnergy
import OAI.Analysis.CircleDomains.Modulus.NormalizedUniformBounds

namespace OAI

/-! Uniform omitted-set and working-disk bounds for the actual compact
scalar models. The constants depend on the source exterior radius alone. -/
open Set Function Metric
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem uniform_omitted_and_image_bound (M : CompactScalarModel G u)
    (harea : ExteriorCoefficientAreaTheorem) (hG : IsOpen G)
    {R : ℝ} (hR : 0 < R)
    (hsource : (((↑) : ℂ → Sphere) '' ball 0 R)ᶜ ⊆ G) :
    (∀ z : ℂ, (z : Sphere) ∉ extendAtInfinity M.function '' G → ‖z‖ ≤ 3*R) ∧
      ∀ z : ℂ, (z : Sphere) ∈ G → ‖z‖ ≤ 4*R → ‖M.function z‖ ≤ 5*R := by
  obtain ⟨hfc,hmap,fi,hfic,hfimap,hl,hr⟩ := M.conformal
  have heq : IsSmoothSphereEquivalence (extendAtInfinity M.function) fi G
      (extendAtInfinity M.function '' G) :=
    ⟨fun p hp => hfc.isSmoothSphereAt hG hp, hmap,
      fun p hp => hfic.isSmoothSphereAt M.image_open hp, hfimap, hl, hr⟩
  have hc : IsConformalOn (extendAtInfinity M.function)
      ((((↑) : ℂ → Sphere) '' closedBall 0 R)ᶜ) := by
    intro p hp
    exact hfc p (hsource ((compl_subset_compl.mpr (image_mono ball_subset_closedBall)) hp))
  obtain ⟨hF,hbound⟩ := normalized_model_uniform_bound harea heq M.image_open hR hsource hc M.normalized
  constructor
  · intro z hz
    obtain ⟨w,hw,he⟩ := hF (z : Sphere) hz
    have hzw : w = z := OnePoint.coe_injective he
    simpa only [hzw, mem_closedBall, dist_zero_right] using hw
  · intro z hz hzr
    obtain ⟨w,hw,he⟩ := hbound z hz hzr
    have hzw : w = M.function z := OnePoint.coe_injective (by simpa only [extendAtInfinity_coe] using he)
    simpa only [hzw, mem_closedBall, dist_zero_right] using hw

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
