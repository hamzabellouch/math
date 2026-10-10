import OAI.Analysis.TracialSplitting.ChallengeDefinitions

namespace OAI

/-! Pullback of a tracial state by a unital star homomorphism. -/
noncomputable section
open scoped ComplexOrder

namespace WeakPureInfiniteness

variable {C D : Type*} [CStarAlgebra C] [CStarAlgebra D]
  [PartialOrder C] [StarOrderedRing C] [PartialOrder D] [StarOrderedRing D]

def tracialStatePullback (τ : Pureness.TracialState D) (f : C →⋆ₐ[ℂ] D) :
    Pureness.TracialState C where
  functional := PositiveLinearMap.mk₀ (τ.functional.toLinearMap.comp f.toLinearMap)
    (fun _ ha => τ.functional.map_nonneg (map_nonneg f ha))
  normalized := by
    change τ.functional (f 1) = 1
    rw [map_one, τ.normalized]
  tracial a b := by
    change τ.functional (f (a * b)) = τ.functional (f (b * a))
    simp only [map_mul f]
    exact τ.tracial (f a) (f b)

lemma tracialStatePullback_apply (τ : Pureness.TracialState D) (f : C →⋆ₐ[ℂ] D)
    (a : C) : (tracialStatePullback τ f).functional a = τ.functional (f a) := rfl

lemma tracialStatePullback_faithful (τ : Pureness.TracialState D) (f : C →⋆ₐ[ℂ] D)
    (hf : Function.Injective f)
    (hτ : ∀ a, τ.functional (star a * a) = 0 → a = 0)
    (a : C) (ha : (tracialStatePullback τ f).functional (star a * a) = 0) : a = 0 := by
  apply hf
  have he : f a = 0 := hτ (f a) (by
    change τ.functional (f (star a * a)) = 0 at ha
    simpa only [map_mul f, map_star f] using ha)
  exact he.trans (map_zero f).symm

end WeakPureInfiniteness

end

end OAI
