import OAI.Analysis.CircleDomains.Selection.PrincipalExteriorGerm
import OAI.Analysis.CircleDomains.Topology.LimitSphereExtension
import OAI.Analysis.CircleDomains.Selection.ExteriorDecay

namespace OAI

/-! The first principal coefficient as a limit. Composition adds the actual
coefficients, and the published area theorem bounds each coefficient on a
fixed exterior disk. -/
open Set Filter Function Asymptotics Bornology
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 def HasPrincipalCoefficient (F : ℂ → ℂ) (b : ℂ) : Prop :=
  Tendsto (fun z => z*(F z-z)) (cobounded ℂ) (𝓝 b)

 theorem HasPrincipalCoefficient.bigO {F : ℂ → ℂ} {b : ℂ}
    (hb : HasPrincipalCoefficient F b) :
    (fun z => F z-z) =O[cobounded ℂ] (fun z => z⁻¹) := by
  have hB : (fun z => z*(F z-z)) =O[cobounded ℂ] (fun _ => (1 : ℂ)) :=
    isBigO_const_of_tendsto hb (by norm_num : (1 : ℂ) ≠ 0)
  have h := (isBigO_refl (fun z : ℂ => z⁻¹) (cobounded ℂ)).mul hB
  apply h.congr' _ (Eventually.of_forall (fun z => mul_one z⁻¹))
  have hn : ∀ᶠ z : ℂ in cobounded ℂ, z ≠ 0 := by
    rw [Metric.cobounded_eq_cocompact]
    exact isCompact_singleton.compl_mem_cocompact
  filter_upwards [hn] with z hz
  simp [hz]

 theorem hasPrincipalCoefficient_of_expansion {F T : ℂ → ℂ} {b : ℂ}
    (hT : ContinuousAt T 0)
    (hexp : ∀ z : ℂ, z ≠ 0 → F z-z = b*z⁻¹+z⁻¹^2*T z⁻¹) :
    HasPrincipalCoefficient F b := by
  have hi := tendsto_inv₀_cobounded (α := ℂ)
  have hlim := (tendsto_const_nhds (x := b)).add (hi.mul (hT.tendsto.comp hi))
  simp only [zero_mul, add_zero] at hlim
  apply hlim.congr'
  have hn : ∀ᶠ z : ℂ in cobounded ℂ, z ≠ 0 := by
    rw [Metric.cobounded_eq_cocompact]
    exact isCompact_singleton.compl_mem_cocompact
  filter_upwards [hn] with z hz
  dsimp only [Function.comp_apply]
  rw [hexp z hz]
  field_simp

 theorem exists_principal_coefficient {F : ℂ → ℂ}
    (hd : ∀ᶠ z in cobounded ℂ, DifferentiableAt ℂ F z)
    (hn : (fun z => F z-z) =O[cobounded ℂ] (fun z => z⁻¹)) :
    ∃ b, HasPrincipalCoefficient F b := by
  obtain ⟨b, T, hT, hexp⟩ := principal_exterior_expansion hd (principal_remainder_tendsto_zero hn)
  exact ⟨b, hasPrincipalCoefficient_of_expansion hT.continuousAt hexp⟩

 theorem HasPrincipalCoefficient.comp {F P : ℂ → ℂ} {b c : ℂ}
    (hb : HasPrincipalCoefficient F b) (hc : HasPrincipalCoefficient P c) :
    HasPrincipalCoefficient (P ∘ F) (b+c) := by
  have hFt := principal_tendsto_cobounded hb.bigO
  have hF0 := principal_remainder_tendsto_zero hb.bigO
  have hP0 := (principal_remainder_tendsto_zero hc.bigO).comp hFt
  have hh := ((Filter.Tendsto.comp hc hFt).sub (hF0.mul hP0)).add hb
  simp only [zero_mul, sub_zero] at hh
  rw [add_comm b c]
  apply hh.congr'
  filter_upwards [] with z
  dsimp only [Function.comp_apply]
  ring

 theorem HasPrincipalCoefficient.norm_le_of_exterior
    {F : ℂ → ℂ} {b : ℂ} (hb : HasPrincipalCoefficient F b)
    (harea : ExteriorCoefficientAreaTheorem) {R : ℝ} (hR : 0 < R)
    (hd : DifferentiableOn ℂ F {z | R < ‖z‖}) (hinj : InjOn F {z | R < ‖z‖}) :
    ‖b‖ ≤ 2*R^2 := by
  apply le_of_tendsto hb.norm
  have he := harea.scaled_exterior_decay hR hd hinj hb.bigO
  filter_upwards [eventually_cobounded_le_norm (E := ℂ) (2*R)] with z hz
  have hn : 0 < ‖z‖ := lt_of_lt_of_le (by positivity) hz
  rw [norm_mul]
  calc
    ‖z‖ * ‖F z-z‖ ≤ ‖z‖ * (2*R^2/‖z‖) := mul_le_mul_of_nonneg_left (he z hz) (norm_nonneg _)
    _ = 2*R^2 := by field_simp

end CircleDomainRigidity

end

end OAI
