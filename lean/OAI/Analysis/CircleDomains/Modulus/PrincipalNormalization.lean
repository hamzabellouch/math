import OAI.Analysis.CircleDomains.Modulus.LaurentNormalization
import OAI.Analysis.CircleDomains.Modulus.NormalizedMetricUniformization

namespace OAI

/-!
# Affine principal normalization of a sphere map

The analytic remainder at zero is bounded near zero. After inversion
this gives the actual O(1/z) remainder at infinity, rather than only a
formal Laurent coefficient calculation.
-/

open Set Filter Function Asymptotics Bornology
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

def IsPrincipalNormalized (f : Sphere → Sphere) : Prop :=
  f OnePoint.infty = OnePoint.infty ∧
    (fun z : ℂ => finiteCoord (f (z : Sphere)) - z) =O[cobounded ℂ] (fun z => z⁻¹)

theorem affine_normalization_bigO
    {f : Sphere → Sphere} {U : Set Sphere} (hU : IsOpen U) (hf : IsConformalOn f U)
    (hinf : OnePoint.infty ∈ U) (hfix : f OnePoint.infty = OnePoint.infty) :
    ∃ a b : ℂ, a ≠ 0 ∧
      (fun z : ℂ => a * finiteCoord (f (z : Sphere)) + b - z) =O[cobounded ℂ] (fun z => z⁻¹) := by
  obtain ⟨a, b, R, ha, hR, hexp⟩ := affine_normalization_expansion hU hf hinf hfix
  have hb : (fun z : ℂ => R z⁻¹) =O[cobounded ℂ] (fun _ => (1 : ℂ)) := by
    simpa only [Function.comp_def] using
      (hR.continuousAt.isBigO (F := ℂ)).comp_tendsto (tendsto_inv₀_cobounded (α := ℂ))
  have hp := (isBigO_refl (fun z : ℂ => z⁻¹) (cobounded ℂ)).mul hb
  refine ⟨a, b, ha, hp.congr' ?_ ?_⟩
  · have hn : ∀ᶠ z : ℂ in cobounded ℂ, z ≠ 0 := by
      rw [Metric.cobounded_eq_cocompact]
      exact (isCompact_singleton.compl_mem_cocompact : {0}ᶜ ∈ cocompact ℂ)
    filter_upwards [hn] with z hz
    change z⁻¹ * R z⁻¹ = a * finiteCoord (f (z : Sphere)) + b - z
    rw [hexp z hz]
    ring
  · exact Eventually.of_forall (fun z => mul_one z⁻¹)

theorem principal_normalize_at_infty
    {f : Sphere → Sphere} {U : Set Sphere} (hU : IsOpen U) (hf : IsConformalOn f U)
    (hinj : InjOn f U) (hinf : OnePoint.infty ∈ U)
    (hfix : f OnePoint.infty = OnePoint.infty) :
    ∃ (a b : ℂ) (ha : a ≠ 0), IsPrincipalNormalized (affineSphere a b ha ∘ f) := by
  obtain ⟨a, b, ha, hbig⟩ := affine_normalization_bigO hU hf hinf hfix
  refine ⟨a, b, ha, ?_, ?_⟩
  · simp only [Function.comp_apply, hfix, affineSphere_infty]
  · have hm : ∀ᶠ z : ℂ in cobounded ℂ, (z : Sphere) ∈ U := by
      have hm := OnePoint.tendsto_coe_infty (hU.mem_nhds hinf)
      change {z : ℂ | (z : Sphere) ∈ U} ∈ cobounded ℂ
      rw [Metric.cobounded_eq_cocompact]
      rw [coclosedCompact_eq_cocompact] at hm
      exact hm
    apply hbig.congr' _ EventuallyEq.rfl
    filter_upwards [hm] with z hz
    have hfin := finite_image_of_fixes_infty hinj hinf hfix hz
    have hp : f (z : Sphere) = ((finiteCoord (f (z : Sphere)) : ℂ) : Sphere) :=
      (CannonMobius.coe_coordinate hfin).symm
    have he := congrArg (fun p : Sphere => finiteCoord (affineSphere a b ha p)) hp
    simpa only [Function.comp_apply, affineSphere_coe, finiteCoord_coe] using
      congrArg (fun w : ℂ => w - z) he.symm

end CircleDomainRigidity

end

end OAI
