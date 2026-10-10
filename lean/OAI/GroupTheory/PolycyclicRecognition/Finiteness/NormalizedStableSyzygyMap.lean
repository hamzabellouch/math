import OAI.GroupTheory.PolycyclicRecognition.Finiteness.NormalizedSyzygyFunctor
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.StableResolutionIdentity

namespace OAI

/-! # Additivity of normalized syzygy maps modulo projective factors

The normalized free cover is not additive. Its induced syzygy map is additive
in the stable quotient; changing a lift produces a map through a free module.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
attribute [local instance 2300] Submodule.Quotient.module
variable {G : Type} [Group G] {A B : Rep.{0} ℤ G}

theorem normalizedSyzygy_stable_of_lift (f : A ⟶ B)
    (l : normalizedFreeRepresentation A ⟶ normalizedFreeRepresentation B)
    (hl : l ≫ normalizedFreeAugmentation B = normalizedFreeAugmentation A ≫ f)
    (s : normalizedSyzygy A ⟶ normalizedSyzygy B)
    (hs : s ≫ kernel.ι (normalizedFreeAugmentation B) =
      kernel.ι (normalizedFreeAugmentation A) ≫ l) :
    stableRepresentationClass _ _ (normalizedSyzygyMap f) = stableRepresentationClass _ _ s := by
  let d := normalizedFreeMap f - l
  have hd : d ≫ normalizedFreeAugmentation B = 0 := by
    dsimp only [d]
    rw [Preadditive.sub_comp, normalizedFreeAugmentation_natural, hl, sub_self]
  let v := kernel.lift (normalizedFreeAugmentation B) d hd
  apply (stableRepresentationClass_eq_iff_projective_factor _ _).mpr
  refine ⟨normalizedFreeRepresentation A, inferInstance,
    kernel.ι (normalizedFreeAugmentation A), v, ?_⟩
  apply (cancel_mono (kernel.ι (normalizedFreeAugmentation B))).mp
  rw [Category.assoc, kernel.lift_ι, Preadditive.sub_comp, normalizedSyzygyMap_ι, hs]
  exact Preadditive.comp_sub _ _ _

def normalizedSyzygyStableLinearMap (A B : Rep.{0} ℤ G) :
    (A ⟶ B) →ₗ[ℤ] StableRepresentationHom (normalizedSyzygy A) (normalizedSyzygy B) := by
  let a : (A ⟶ B) →+ StableRepresentationHom (normalizedSyzygy A) (normalizedSyzygy B) :=
    AddMonoidHom.mk' (fun f => stableRepresentationClass _ _ (normalizedSyzygyMap f)) (by
      intro f g
      have h := normalizedSyzygy_stable_of_lift (f + g)
        (normalizedFreeMap f + normalizedFreeMap g)
        (by simp only [Preadditive.add_comp, Preadditive.comp_add, normalizedFreeAugmentation_natural])
        (normalizedSyzygyMap f + normalizedSyzygyMap g)
        (by simp only [Preadditive.add_comp, Preadditive.comp_add, normalizedSyzygyMap_ι])
      exact h.trans (map_add _ _ _))
  exact { a with map_smul' := fun r f => map_intCast_smul a ℤ ℤ r f }

theorem normalizedSyzygyStableLinearMap_eq_zero (f : A ⟶ B)
    (hf : stableRepresentationClass A B f = 0) : normalizedSyzygyStableLinearMap A B f = 0 := by
  obtain ⟨P, hP, u, v, huv⟩ := (stableRepresentationClass_eq_zero_iff_projective_factor f).mp hf
  let := hP
  let a := Projective.factorThru v (normalizedFreeAugmentation B)
  have ha : a ≫ normalizedFreeAugmentation B = v := Projective.factorThru_comp _ _
  have h := normalizedSyzygy_stable_of_lift f (normalizedFreeAugmentation A ≫ u ≫ a)
    (by rw [Category.assoc, Category.assoc, ha, huv]) 0 (by
      rw [zero_comp, ← Category.assoc, ← Category.assoc, kernel.condition,
        zero_comp, zero_comp])
  exact h.trans ((stableRepresentationClass _ _).map_zero)

def normalizedStableSyzygyMap (A B : Rep.{0} ℤ G) :
    StableRepresentationHom A B →ₗ[ℤ]
      StableRepresentationHom (normalizedSyzygy A) (normalizedSyzygy B) :=
  (projectiveFactorSubmodule A B).liftQ (normalizedSyzygyStableLinearMap A B) (by
    intro f hf
    apply normalizedSyzygyStableLinearMap_eq_zero f
    exact (Submodule.Quotient.mk_eq_zero _).mpr hf)

@[simp]
theorem normalizedStableSyzygyMap_class (f : A ⟶ B) :
    normalizedStableSyzygyMap A B (stableRepresentationClass A B f) =
      stableRepresentationClass _ _ (normalizedSyzygyMap f) := rfl

def normalizedStableSyzygyIterate (A B : Rep.{0} ℤ G) :
    (n : ℕ) → StableRepresentationHom A B →ₗ[ℤ]
      StableRepresentationHom ((iteratedNormalizedSyzygy n).obj A)
        ((iteratedNormalizedSyzygy n).obj B)
  | 0 => LinearMap.id
  | n + 1 => (normalizedStableSyzygyMap ((iteratedNormalizedSyzygy n).obj A)
      ((iteratedNormalizedSyzygy n).obj B)).comp (normalizedStableSyzygyIterate A B n)

@[simp]
theorem normalizedStableSyzygyIterate_class (n : ℕ) (f : A ⟶ B) :
    normalizedStableSyzygyIterate A B n (stableRepresentationClass A B f) =
      stableRepresentationClass _ _ ((iteratedNormalizedSyzygy n).map f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change normalizedStableSyzygyMap _ _
      (normalizedStableSyzygyIterate A B n (stableRepresentationClass A B f)) = _
    rw [ih, normalizedStableSyzygyMap_class]
    rfl

end PolycyclicRecognition

end

end OAI
