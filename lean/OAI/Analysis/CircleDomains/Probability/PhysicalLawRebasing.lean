import OAI.Analysis.CircleDomains.Probability.PhysicalOccupationCode
import OAI.Analysis.CircleDomains.Probability.PhysicalOccupationPushforward

namespace OAI

/-! Physical length and occupation do not depend on the fallback point at dust
parameters. This permits a recursive law to use the original domain presentation. -/
open Set Function MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    {G : Set Y} {U : Set X}

 theorem physicalDomainLength_basePoint (e : G ≃ₜ U) (y₁ y₂ : Y)
    (γ : C(PathTime, X)) : physicalDomainLength e y₁ γ = physicalDomainLength e y₂ γ := by
  unfold physicalDomainLength physicalStageLength
  congr 1
  funext n
  apply Finset.sum_congr rfl
  intro i _
  unfold physicalDyadicLength physicalDyadicPath totalPhysicalSubpath
  split_ifs
  · rfl
  · have hz (y : Y) : eVariationOn (ContinuousMap.const PathTime y) univ = 0 := by
      apply (eVariationOn.eq_zero_iff _).mpr
      intro _ _ _ _
      exact edist_self y
    rw [hz, hz]


variable [MeasurableSpace Y] [BorelSpace Y]

 theorem physicalStageOccupation_basePoint (e : G ≃ₜ U) (y₁ y₂ : Y)
    (n : ℕ) (γ : C(PathTime, X)) :
    physicalStageOccupation e y₁ n γ = physicalStageOccupation e y₂ n γ := by
  unfold physicalStageOccupation
  apply Finset.sum_congr rfl
  intro i _
  unfold physicalDyadicPath totalPhysicalSubpath
  split_ifs
  · rfl
  · simp only [rectifiableOccupationCode_const]

 theorem physicalOccupationCode_basePoint (e : G ≃ₜ U) (y₁ y₂ : Y)
    (γ : C(PathTime, X)) : physicalOccupationCode e y₁ γ = physicalOccupationCode e y₂ γ := by
  have hlen := physicalDomainLength_basePoint e y₁ y₂ γ
  unfold physicalOccupationCode
  split_ifs with h₁ h₂ h₂
  · apply Measure.ext
    intro s hs
    rw [dyadicPhysicalOccupation_apply _ _ _ hs, dyadicPhysicalOccupation_apply _ _ _ hs]
    simp only [physicalStageOccupation_basePoint e y₁ y₂]
  · exact (h₂ (hlen ▸ h₁)).elim
  · exact (h₁ (hlen.symm ▸ h₂)).elim
  · rfl

 omit [MeasurableSpace Y] [BorelSpace Y] in
 theorem domainEquiv_eq_of_projection {G₁ G₂ : Set Y} {U₁ U₂ : Set X}
    (e₁ : G₁ ≃ₜ U₁) (e₂ : G₂ ≃ₜ U₂) (hG : G₁ = G₂) (hU : U₁ = U₂)
    (π : Y → X) (he₁ : ∀ x : G₁, (e₁ x).val = π x.val)
    (he₂ : ∀ x : G₂, (e₂ x).val = π x.val) :
    HEq e₁ e₂ := by
  subst G₂
  subst U₂
  apply heq_of_eq
  ext x
  exact (he₁ x).trans (he₂ x).symm

 omit [MeasurableSpace Y] [BorelSpace Y] in
 theorem physicalDomainLength_congr_projection {G₁ G₂ : Set Y} {U₁ U₂ : Set X}
    (e₁ : G₁ ≃ₜ U₁) (e₂ : G₂ ≃ₜ U₂) (hG : G₁ = G₂) (hU : U₁ = U₂)
    (π : Y → X) (he₁ : ∀ x : G₁, (e₁ x).val = π x.val)
    (he₂ : ∀ x : G₂, (e₂ x).val = π x.val) (y₁ y₂ : Y) (γ : C(PathTime, X)) :
    physicalDomainLength e₁ y₁ γ = physicalDomainLength e₂ y₂ γ := by
  have he := domainEquiv_eq_of_projection e₁ e₂ hG hU π he₁ he₂
  subst G₂
  subst U₂
  cases eq_of_heq he
  exact physicalDomainLength_basePoint e₁ y₁ y₂ γ

 theorem physicalOccupationCode_congr_projection {G₁ G₂ : Set Y} {U₁ U₂ : Set X}
    (e₁ : G₁ ≃ₜ U₁) (e₂ : G₂ ≃ₜ U₂) (hG : G₁ = G₂) (hU : U₁ = U₂)
    (π : Y → X) (he₁ : ∀ x : G₁, (e₁ x).val = π x.val)
    (he₂ : ∀ x : G₂, (e₂ x).val = π x.val) (y₁ y₂ : Y) (γ : C(PathTime, X)) :
    physicalOccupationCode e₁ y₁ γ = physicalOccupationCode e₂ y₂ γ := by
  have he := domainEquiv_eq_of_projection e₁ e₂ hG hU π he₁ he₂
  subst G₂
  subst U₂
  cases eq_of_heq he
  exact physicalOccupationCode_basePoint e₁ y₁ y₂ γ

variable [MeasurableSpace C(PathTime, X)]
 theorem meanPhysicalOccupation_congr_projection {G₁ G₂ : Set Y} {U₁ U₂ : Set X}
    (e₁ : G₁ ≃ₜ U₁) (e₂ : G₂ ≃ₜ U₂) (hG : G₁ = G₂) (hU : U₁ = U₂)
    (π : Y → X) (he₁ : ∀ x : G₁, (e₁ x).val = π x.val)
    (he₂ : ∀ x : G₂, (e₂ x).val = π x.val) (y₁ y₂ : Y)
    (μ : ProbabilityMeasure C(PathTime, X)) :
    meanPhysicalOccupation e₁ y₁ μ = meanPhysicalOccupation e₂ y₂ μ := by
  unfold meanPhysicalOccupation
  congr 1
  funext γ
  exact physicalOccupationCode_congr_projection e₁ e₂ hG hU π he₁ he₂ y₁ y₂ γ

end CircleDomainRigidity

end

end OAI
