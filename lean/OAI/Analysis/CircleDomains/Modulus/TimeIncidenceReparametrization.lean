import OAI.Analysis.CircleDomains.Modulus.CountableImageIncidence

namespace OAI

/-! Incidence and multiplicity-sensitive tolls under an injective change
of path parameter. These formulas also apply to a restricted interval. -/

open Set Function
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {S T X Z : Type*}

theorem timeIncidence_image (R : Set (Z × X)) (γ : T → X) (f : S → T) (A : Set S) :
    timeIncidence R γ (f '' A) = timeIncidence R (γ ∘ f) A := by
  ext z
  constructor
  · rintro ⟨t, ⟨s, hs, rfl⟩, hr⟩
    exact ⟨s, hs, hr⟩
  · rintro ⟨s, hs, hr⟩
    exact ⟨f s, ⟨s, hs, rfl⟩, hr⟩

theorem timeToll_image (γ : T → X) (f : S → T) (hf : Injective f)
    (A : Set S) (m : X → ℝ≥0∞) :
    timeToll γ (f '' A) m = timeToll (γ ∘ f) A m := by
  exact ((Equiv.Set.image f A hf).tsum_eq (fun t => m (γ t))).symm

theorem image_preimage_inter_eq (f : S → T) (A : Set T) (I : Set S) :
    f '' (f ⁻¹' A ∩ I) = A ∩ f '' I := by
  ext t
  constructor
  · rintro ⟨s, ⟨hs, hi⟩, rfl⟩
    exact ⟨hs, s, hi, rfl⟩
  · rintro ⟨ht, s, hi, rfl⟩
    exact ⟨s, ⟨ht, hi⟩, rfl⟩

theorem timeIncidence_restrict (R : Set (Z × X)) (γ : T → X)
    (f : S → T) (A : Set T) (I : Set S) :
    timeIncidence R γ (A ∩ f '' I) = timeIncidence R (γ ∘ f) (f ⁻¹' A ∩ I) := by
  rw [← image_preimage_inter_eq, timeIncidence_image]

theorem timeToll_restrict (γ : T → X) (f : S → T) (hf : Injective f)
    (A : Set T) (I : Set S) (m : X → ℝ≥0∞) :
    timeToll γ (A ∩ f '' I) m = timeToll (γ ∘ f) (f ⁻¹' A ∩ I) m := by
  rw [← image_preimage_inter_eq, timeToll_image γ f hf]

end CircleDomainRigidity

end

end OAI
