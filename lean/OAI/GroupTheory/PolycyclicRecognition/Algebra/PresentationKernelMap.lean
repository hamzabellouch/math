import OAI.GroupTheory.PolycyclicRecognition.Finiteness.ProjectivePresentationComparison

namespace OAI

/-! # The stable kernel map of a short exact sequence

A lift of the normalized free cover of the quotient gives a map from its
syzygy to the submodule. Changing the lift changes this map by a projective
factor, and the construction is natural in the stable quotient.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

def presentationKernelMapOfLift (S : ShortComplex (Rep.{0} ℤ G))
    (hS : S.ShortExact) (l : normalizedFreeRepresentation S.X₃ ⟶ S.X₂)
    (hl : l ≫ S.g = normalizedFreeAugmentation S.X₃) :
    normalizedSyzygy S.X₃ ⟶ S.X₁ := by
  let : Mono S.f := hS.mono_f
  exact hS.exact.lift (kernel.ι (normalizedFreeAugmentation S.X₃) ≫ l)
    (by rw [Category.assoc, hl, kernel.condition])

@[reassoc]
theorem presentationKernelMapOfLift_f (S : ShortComplex (Rep.{0} ℤ G))
    (hS : S.ShortExact) (l : normalizedFreeRepresentation S.X₃ ⟶ S.X₂)
    (hl : l ≫ S.g = normalizedFreeAugmentation S.X₃) :
    presentationKernelMapOfLift S hS l hl ≫ S.f =
      kernel.ι (normalizedFreeAugmentation S.X₃) ≫ l := by
  let : Mono S.f := hS.mono_f
  exact hS.exact.lift_f _ _

theorem presentationKernelMapOfLift_stable_natural
    {S T : ShortComplex (Rep.{0} ℤ G)} (hS : S.ShortExact) (hT : T.ShortExact)
    (φ : S ⟶ T)
    (lS : normalizedFreeRepresentation S.X₃ ⟶ S.X₂)
    (hlS : lS ≫ S.g = normalizedFreeAugmentation S.X₃)
    (lT : normalizedFreeRepresentation T.X₃ ⟶ T.X₂)
    (hlT : lT ≫ T.g = normalizedFreeAugmentation T.X₃) :
    stableRepresentationClass _ _
      (normalizedSyzygyMap φ.τ₃ ≫ presentationKernelMapOfLift T hT lT hlT) =
    stableRepresentationClass _ _
      (presentationKernelMapOfLift S hS lS hlS ≫ φ.τ₁) := by
  let : Mono T.f := hT.mono_f
  let d := normalizedFreeMap φ.τ₃ ≫ lT - lS ≫ φ.τ₂
  have hd : d ≫ T.g = 0 := by
    dsimp only [d]
    rw [Preadditive.sub_comp, Category.assoc, hlT,
      Category.assoc, φ.comm₂₃, ← Category.assoc, hlS,
      normalizedFreeAugmentation_natural, sub_self]
  let v := hT.exact.lift d hd
  apply (stableRepresentationClass_eq_iff_projective_factor _ _).mpr
  refine ⟨normalizedFreeRepresentation S.X₃, inferInstance,
    kernel.ι (normalizedFreeAugmentation S.X₃), v, ?_⟩
  apply (cancel_mono T.f).mp
  rw [Category.assoc, hT.exact.lift_f, Preadditive.sub_comp,
    Category.assoc, presentationKernelMapOfLift_f,
    ← Category.assoc, normalizedSyzygyMap_ι, Category.assoc,
    Category.assoc, φ.comm₁₂, presentationKernelMapOfLift_f_assoc]
  exact Preadditive.comp_sub _ _ _

def presentationFreeLift (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    normalizedFreeRepresentation S.X₃ ⟶ S.X₂ := by
  let : Epi S.g := hS.epi_g
  exact Projective.factorThru (normalizedFreeAugmentation S.X₃) S.g

@[reassoc]
theorem presentationFreeLift_g (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    presentationFreeLift S hS ≫ S.g = normalizedFreeAugmentation S.X₃ := by
  let : Epi S.g := hS.epi_g
  exact Projective.factorThru_comp _ _

def presentationKernelMap (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    normalizedSyzygy S.X₃ ⟶ S.X₁ :=
  presentationKernelMapOfLift S hS (presentationFreeLift S hS) (presentationFreeLift_g S hS)

@[reassoc]
theorem presentationKernelMap_f (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    presentationKernelMap S hS ≫ S.f =
      kernel.ι (normalizedFreeAugmentation S.X₃) ≫ presentationFreeLift S hS :=
  presentationKernelMapOfLift_f S hS _ _

theorem presentationKernelMap_stable_natural
    {S T : ShortComplex (Rep.{0} ℤ G)} (hS : S.ShortExact) (hT : T.ShortExact)
    (φ : S ⟶ T) :
    stableRepresentationClass _ _ (normalizedSyzygyMap φ.τ₃ ≫ presentationKernelMap T hT) =
      stableRepresentationClass _ _ (presentationKernelMap S hS ≫ φ.τ₁) :=
  presentationKernelMapOfLift_stable_natural hS hT φ _ _ _ _

theorem presentationKernelMap_f_stable_zero
    (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    stableRepresentationClass _ _ (presentationKernelMap S hS ≫ S.f) = 0 := by
  apply (stableRepresentationClass_eq_zero_iff_projective_factor _).mpr
  exact ⟨normalizedFreeRepresentation S.X₃, inferInstance,
    kernel.ι (normalizedFreeAugmentation S.X₃), presentationFreeLift S hS,
    (presentationKernelMap_f S hS).symm⟩

theorem presentationKernelMap_g_stable_zero
    (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    stableRepresentationClass _ _ (normalizedSyzygyMap S.g ≫ presentationKernelMap S hS) = 0 := by
  let : Mono S.f := hS.mono_f
  let d := normalizedFreeMap S.g ≫ presentationFreeLift S hS - normalizedFreeAugmentation S.X₂
  have hd : d ≫ S.g = 0 := by
    dsimp only [d]
    rw [Preadditive.sub_comp, Category.assoc, presentationFreeLift_g,
      normalizedFreeAugmentation_natural, sub_self]
  let v := hS.exact.lift d hd
  apply (stableRepresentationClass_eq_zero_iff_projective_factor _).mpr
  refine ⟨normalizedFreeRepresentation S.X₂, inferInstance,
    kernel.ι (normalizedFreeAugmentation S.X₂), v, ?_⟩
  apply (cancel_mono S.f).mp
  rw [Category.assoc, hS.exact.lift_f, Category.assoc, presentationKernelMap_f,
    ← Category.assoc, normalizedSyzygyMap_ι]
  dsimp only [d]
  rw [Preadditive.comp_sub, kernel.condition, sub_zero, Category.assoc]

theorem presentationKernelMap_stable_zero_of_section
    (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact)
    (s : S.X₃ ⟶ S.X₂) (hs : s ≫ S.g = 𝟙 S.X₃) :
    stableRepresentationClass _ _ (presentationKernelMap S hS) = 0 := by
  let : Mono S.f := hS.mono_f
  let d := presentationFreeLift S hS - normalizedFreeAugmentation S.X₃ ≫ s
  have hd : d ≫ S.g = 0 := by
    dsimp only [d]
    rw [Preadditive.sub_comp, presentationFreeLift_g, Category.assoc, hs,
      Category.comp_id, sub_self]
  let v := hS.exact.lift d hd
  apply (stableRepresentationClass_eq_zero_iff_projective_factor _).mpr
  refine ⟨normalizedFreeRepresentation S.X₃, inferInstance,
    kernel.ι (normalizedFreeAugmentation S.X₃), v, ?_⟩
  apply (cancel_mono S.f).mp
  rw [Category.assoc, hS.exact.lift_f, presentationKernelMap_f]
  dsimp only [d]
  rw [Preadditive.comp_sub, ← Category.assoc, kernel.condition, zero_comp, sub_zero]

theorem presentationKernelMap_stable_inverse
    (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) [Projective S.X₂] :
    ∃ b : S.X₁ ⟶ normalizedSyzygy S.X₃,
      stableRepresentationClass _ _ (presentationKernelMap S hS ≫ b) =
        stableRepresentationClass _ _ (𝟙 _) ∧
      stableRepresentationClass _ _ (b ≫ presentationKernelMap S hS) =
        stableRepresentationClass _ _ (𝟙 _) := by
  let : Mono S.f := hS.mono_f
  let F := normalizedFreeRepresentation S.X₃
  let ε := normalizedFreeAugmentation S.X₃
  let l := presentationFreeLift S hS
  have hl : l ≫ S.g = ε := presentationFreeLift_g S hS
  let r : S.X₂ ⟶ F := Projective.factorThru S.g ε
  have hr : r ≫ ε = S.g := Projective.factorThru_comp _ _
  have hbr : (S.f ≫ r) ≫ ε = 0 := by rw [Category.assoc, hr, S.zero]
  let b : S.X₁ ⟶ normalizedSyzygy S.X₃ := kernel.lift ε (S.f ≫ r) hbr
  have hb : b ≫ kernel.ι ε = S.f ≫ r := kernel.lift_ι _ _ _
  have ha : presentationKernelMap S hS ≫ S.f = kernel.ι ε ≫ l :=
    presentationKernelMap_f S hS
  refine ⟨b, ?_, ?_⟩
  · have hd : (l ≫ r - 𝟙 F) ≫ ε = 0 := by
      rw [Preadditive.sub_comp, Category.assoc, hr, hl, Category.id_comp, sub_self]
    let v : F ⟶ normalizedSyzygy S.X₃ := kernel.lift ε (l ≫ r - 𝟙 F) hd
    apply (stableRepresentationClass_eq_iff_projective_factor _ _).mpr
    refine ⟨F, inferInstance, kernel.ι ε, v, ?_⟩
    apply (cancel_mono (kernel.ι ε)).mp
    rw [Category.assoc, kernel.lift_ι, Preadditive.sub_comp, Category.assoc,
      hb, ← Category.assoc, ha, Category.assoc, Category.id_comp,
      Preadditive.comp_sub, Category.comp_id]
  · have hd : (r ≫ l - 𝟙 S.X₂) ≫ S.g = 0 := by
      rw [Preadditive.sub_comp, Category.assoc, hl, hr, Category.id_comp, sub_self]
    let v : S.X₂ ⟶ S.X₁ := hS.exact.lift (r ≫ l - 𝟙 S.X₂) hd
    apply (stableRepresentationClass_eq_iff_projective_factor _ _).mpr
    refine ⟨S.X₂, inferInstance, S.f, v, ?_⟩
    apply (cancel_mono S.f).mp
    rw [Category.assoc, hS.exact.lift_f, Preadditive.sub_comp, Category.assoc,
      ha, ← Category.assoc, hb, Category.assoc, Category.id_comp,
      Preadditive.comp_sub, Category.comp_id]

end PolycyclicRecognition

end

end OAI
