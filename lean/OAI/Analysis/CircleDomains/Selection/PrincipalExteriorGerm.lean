import OAI.Analysis.CircleDomains.Modulus.PrincipalNormalization
import Mathlib.Analysis.Complex.RemovableSingularity

namespace OAI

/-! A holomorphic exterior map tending to the identity has an actual
principal Laurent germ. The first two divided differences give the
coefficient and the analytic remainder; no Laurent estimate is assumed. -/
open Set Filter Function Asymptotics Bornology
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 def invertedPrincipalRemainder (F : ℂ → ℂ) : ℂ → ℂ :=
  Function.update (fun w => F w⁻¹ - w⁻¹) 0 0

 theorem invertedPrincipalRemainder_analytic {F : ℂ → ℂ}
    (hF : ∀ᶠ z in cobounded ℂ, DifferentiableAt ℂ F z)
    (ht : Tendsto (fun z => F z - z) (cobounded ℂ) (𝓝 0)) :
    AnalyticAt ℂ (invertedPrincipalRemainder F) 0 := by
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
  · have hd := (tendsto_inv₀_nhdsNE_zero (α := ℂ)).eventually hF
    filter_upwards [hd, self_mem_nhdsWithin] with w hw hw0
    have hn : w ≠ 0 := hw0
    have hi : DifferentiableAt ℂ (fun z : ℂ => z⁻¹) w := differentiableAt_inv hn
    have hh := (hw.comp w hi).sub hi
    apply hh.congr_of_eventuallyEq
    filter_upwards [isOpen_ne.mem_nhds hn] with z hz
    exact Function.update_of_ne hz _ _
  · exact continuousAt_update_same.mpr
      (ht.comp (tendsto_inv₀_nhdsNE_zero (α := ℂ)))

 theorem principal_exterior_expansion {F : ℂ → ℂ}
    (hF : ∀ᶠ z in cobounded ℂ, DifferentiableAt ℂ F z)
    (ht : Tendsto (fun z => F z - z) (cobounded ℂ) (𝓝 0)) :
    ∃ (c : ℂ) (T : ℂ → ℂ), AnalyticAt ℂ T 0 ∧
      ∀ z : ℂ, z ≠ 0 → F z - z = c * z⁻¹ + z⁻¹ ^ 2 * T z⁻¹ := by
  let u := invertedPrincipalRemainder F
  have hu : AnalyticAt ℂ u 0 := invertedPrincipalRemainder_analytic hF ht
  have hu0 : u 0 = 0 := Function.update_self _ _ _
  let v := dslope u 0
  let T := dslope v 0
  have hv : AnalyticAt ℂ v 0 := analyticAt_dslope_zero hu
  refine ⟨v 0, T, analyticAt_dslope_zero hv, ?_⟩
  intro z hz
  have h1 : z⁻¹ * v z⁻¹ = u z⁻¹ := by
    simpa only [sub_zero, smul_eq_mul, hu0] using sub_smul_dslope u 0 z⁻¹
  have h2 : z⁻¹ * T z⁻¹ = v z⁻¹ - v 0 := by
    simpa only [sub_zero, smul_eq_mul] using sub_smul_dslope v 0 z⁻¹
  have he : u z⁻¹ = F z - z := by
    dsimp only [u, invertedPrincipalRemainder]
    rw [Function.update_of_ne (inv_ne_zero hz), inv_inv]
  rw [he] at h1
  linear_combination -h1 - z⁻¹ * h2

 theorem principal_bigO_of_exterior_holomorphic {F : ℂ → ℂ}
    (hF : ∀ᶠ z in cobounded ℂ, DifferentiableAt ℂ F z)
    (ht : Tendsto (fun z => F z - z) (cobounded ℂ) (𝓝 0)) :
    (fun z => F z - z) =O[cobounded ℂ] (fun z => z⁻¹) := by
  let u := invertedPrincipalRemainder F
  have hu : AnalyticAt ℂ u 0 := invertedPrincipalRemainder_analytic hF ht
  have hu0 : u 0 = 0 := Function.update_self _ _ _
  let v := dslope u 0
  have hv : AnalyticAt ℂ v 0 := analyticAt_dslope_zero hu
  have hb : (fun z : ℂ => v z⁻¹) =O[cobounded ℂ] (fun _ => (1 : ℂ)) := by
    simpa only [Function.comp_def] using
      (hv.continuousAt.isBigO (F := ℂ)).comp_tendsto (tendsto_inv₀_cobounded (α := ℂ))
  have hp := (isBigO_refl (fun z : ℂ => z⁻¹) (cobounded ℂ)).mul hb
  apply hp.congr'
  · have hn : ∀ᶠ z : ℂ in cobounded ℂ, z ≠ 0 := by
      rw [Metric.cobounded_eq_cocompact]
      exact (isCompact_singleton.compl_mem_cocompact : {0}ᶜ ∈ cocompact ℂ)
    filter_upwards [hn] with z hz
    have hh := sub_smul_dslope u 0 z⁻¹
    simp only [sub_zero, smul_eq_mul] at hh
    change z⁻¹ * v z⁻¹ = u z⁻¹ - u 0 at hh
    rw [hu0, sub_zero] at hh
    simpa only [u, invertedPrincipalRemainder,
      Function.update_of_ne (inv_ne_zero hz), inv_inv] using hh
  · exact Eventually.of_forall (fun z => mul_one z⁻¹)

end CircleDomainRigidity

end

end OAI
