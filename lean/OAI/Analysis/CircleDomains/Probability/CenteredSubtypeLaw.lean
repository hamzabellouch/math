import OAI.Analysis.CircleDomains.Probability.CenteredArcLaw
import OAI.Analysis.CircleDomains.Probability.SupportedProbability

namespace OAI

/-! The compact terminal-arc law supplies the actual supported law and
compact disk-arc image used by the mean stream construction. -/

open Set Function MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

theorem exists_centered_subtype_arc_law (J : ℂ ≃ₜ ℂ) {b : Sphere}
    (hb : b ∈ ((↑) : ℂ → Sphere) '' jordanInterior J)
    (A : Set C(PathTime, Sphere)) (hA : IsCompact A)
    (hAS : A ⊆ terminalArcSet (((↑) : ℂ → Sphere) '' jordanInterior J) b)
    (μ : ProbabilityMeasure C(PathTime, Sphere))
    (hμ : ∀ᵐ γ ∂(μ : Measure C(PathTime, Sphere)), γ ∈ A) :
    ∃ (F : C(Sphere, ℂ)) (K : Set C(PathTime, ℂ)) (η : ProbabilityMeasure A)
      (f : A → K),
      EqOn F (centeredJordanCoordinate J b)
        (closure (((↑) : ℂ → Sphere) '' jordanInterior J)) ∧
      IsCompact K ∧ K ⊆ diskTerminalArcSet ∧ η.map Subtype.val = μ ∧
      Measurable f ∧ (∀ γ : A, (f γ).val = F.comp γ.val) := by
  obtain ⟨F, hF⟩ := exists_centeredJordanExtension J hb
  let K := F.comp '' A
  have hK : IsCompact K := hA.image F.continuous_postcomp
  let η := supportedProbability μ A hA.measurableSet hμ
  let f : A → K := fun γ => ⟨F.comp γ.val, mem_image_of_mem F.comp γ.property⟩
  have hf : Continuous f :=
    (F.continuous_postcomp.comp continuous_subtype_val).subtype_mk _
  refine ⟨F, K, η, f, hF, hK, ?_, supportedProbability_map μ A hA.measurableSet hμ,
    hf.measurable, fun _ => rfl⟩
  rintro _ ⟨γ, hγ, rfl⟩
  exact centeredJordanPath_mem J hb F hF (hAS hγ)

end CircleDomainRigidity

end

end OAI
