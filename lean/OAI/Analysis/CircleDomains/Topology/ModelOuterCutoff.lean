import OAI.Analysis.CircleDomains.Transfer.ModelExteriorEstimate
import OAI.Analysis.CircleDomains.Topology.FixedDiskCutoffs

namespace OAI

/-! A fixed target cutoff changes a source barrier only where the saved
outer collar already vanishes. The sharper exterior remainder gives a
nonempty transition annulus, independent of the finite test list. -/
open Set Function Filter Metric Asymptotics Bornology
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem exterior_decay_bound (M : CompactScalarModel G u)
    (harea : ExteriorCoefficientAreaTheorem) {a : ℝ} (ha : 0 < a)
    (hsource : (((↑) : ℂ → Sphere) '' ball 0 a)ᶜ ⊆ G) :
    ∀ z : ℂ, 2*a ≤ ‖z‖ → ‖M.function z-z‖ ≤ 2*a^2/‖z‖ := by
  have hsub {z : ℂ} (hz : a < ‖z‖) : (z : Sphere) ∈ G := by
    apply hsource
    rintro ⟨w,hw,he⟩
    have hwz : w = z := OnePoint.coe_injective he
    subst w
    have := mem_ball_zero_iff.mp hw
    linarith
  have hf : DifferentiableOn ℂ M.function {z | a < ‖z‖} := fun z hz =>
    (finite_differentiable_of_sphere_conformal (M.conformal.1 _ (hsub hz))).differentiableWithinAt
  have hi : InjOn M.function {z | a < ‖z‖} := by
    intro z hz w hw he
    apply OnePoint.coe_injective
    apply M.conformal.bijOn.injOn (hsub hz) (hsub hw)
    simpa only [extendAtInfinity_coe] using congrArg ((↑) : ℂ → Sphere) he
  have hn : (fun z : ℂ => M.function z-z) =O[cobounded ℂ] (fun z => z⁻¹) := by
    simpa only [extendAtInfinity_coe,finiteCoord_coe] using M.normalized.2
  exact harea.scaled_exterior_decay ha hf hi hn

 theorem exterior_half_bound (M : CompactScalarModel G u)
    (harea : ExteriorCoefficientAreaTheorem) {a : ℝ} (ha : 0 < a)
    (hsource : (((↑) : ℂ → Sphere) '' ball 0 a)ᶜ ⊆ G)
    {z : ℂ} (hz : 4*a ≤ ‖z‖) : ‖M.function z-z‖ ≤ a/2 := by
  have hn : 0 < ‖z‖ := by linarith
  apply (M.exterior_decay_bound harea ha hsource z (by linarith)).trans
  apply (div_le_iff₀ hn).mpr
  nlinarith

 theorem cutoff_preserves_inner_barrier (M : CompactScalarModel G u)
    (harea : ExteriorCoefficientAreaTheorem) (hG : IsOpen G) {a : ℝ} (ha : 0 < a)
    (hsource : (((↑) : ℂ → Sphere) '' ball 0 a)ᶜ ⊆ G)
    (θ : EuclideanPlane → ℝ)
    (hθone : ∀ x ∈ closedBall 0 (64*a), θ x = 1)
    (hθsupp : tsupport θ ⊆ ball 0 ((129/2:ℝ)*a))
    (v : ℂ → ℝ)
    (hv : ∀ z : ℂ, (z : Sphere) ∈ G → 63*a ≤ ‖z‖ → ‖z‖ ≤ 65*a → v z = 0) :
    (∀ z : ℂ, (z : Sphere) ∈ G → ‖z‖ < 65*a →
      θ (complexPlaneCoordinates.symm (M.function z))*v z = v z) ∧
    (∀ z : ℂ, (z : Sphere) ∈ G → 65*a ≤ ‖z‖ →
      θ (complexPlaneCoordinates.symm (M.function z))*v z = 0) := by
  have hn (z : ℂ) : ‖complexPlaneCoordinates.symm z‖ = ‖z‖ := by
    simpa only [complexPlaneCoordinates.apply_symm_apply] using
      (complexPlaneCoordinates_norm (complexPlaneCoordinates.symm z)).symm
  have hθzero (z : ℂ) (hz : (129/2:ℝ)*a ≤ ‖M.function z‖) :
      θ (complexPlaneCoordinates.symm (M.function z)) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hx
    have ht := mem_ball_zero_iff.mp (hθsupp hx)
    rw [hn] at ht
    linarith
  constructor
  · intro z hz hzn
    by_cases hsmall : ‖z‖ ≤ 63*a
    · have hbound : ‖M.function z‖ ≤ 64*a := by
        by_cases h4 : ‖z‖ ≤ 4*a
        · have h := (M.uniform_omitted_and_image_bound harea hG ha hsource).2 z hz h4
          linarith
        · have h := M.exterior_half_bound harea ha hsource (le_of_not_ge h4)
          have ht := norm_le_norm_sub_add (M.function z) z
          linarith
      rw [hθone _ (by simpa only [mem_closedBall,dist_zero_right,hn] using hbound),one_mul]
    · rw [hv z hz (le_of_not_ge hsmall) hzn.le,mul_zero]
  · intro z hz hzn
    have h := M.exterior_half_bound harea ha hsource (by linarith)
    have ht := norm_le_norm_sub_add z (M.function z)
    rw [norm_sub_rev] at ht
    rw [hθzero z (by linarith),zero_mul]

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
