import OAI.GroupTheory.PolycyclicRecognition.Finiteness.CompleteCohomologyMiddleExact
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.CompleteCohomologyConnecting

namespace OAI

/-! # Rotating a short exact sequence using a projective cover -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] Prod.instModule
variable {G : Type} [Group G]

abbrev rotationMiddle (S : ShortComplex (Rep.{0} ℤ G)) : Rep.{0} ℤ G :=
  Rep.of (S.X₁.ρ.prod (normalizedFreeRepresentation S.X₃).ρ)

def rotationFst (S : ShortComplex (Rep.{0} ℤ G)) : rotationMiddle S ⟶ S.X₁ :=
  Rep.ofHom (.fst ℤ _ _)

def rotationSnd (S : ShortComplex (Rep.{0} ℤ G)) :
    rotationMiddle S ⟶ normalizedFreeRepresentation S.X₃ :=
  Rep.ofHom (.snd ℤ _ _)

def rotationInl (S : ShortComplex (Rep.{0} ℤ G)) : S.X₁ ⟶ rotationMiddle S :=
  Rep.ofHom (.inl ℤ _ _)

def rotationInr (S : ShortComplex (Rep.{0} ℤ G)) :
    normalizedFreeRepresentation S.X₃ ⟶ rotationMiddle S :=
  Rep.ofHom (.inr ℤ _ _)

def rotationProjection (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    rotationMiddle S ⟶ S.X₂ :=
  rotationFst S ≫ S.f + rotationSnd S ≫ presentationFreeLift S hS

def rotationInclusion (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    normalizedSyzygy S.X₃ ⟶ rotationMiddle S :=
  Rep.ofHom ((presentationKernelMap S hS).hom.prod
    (-(kernel.ι (normalizedFreeAugmentation S.X₃))).hom)

theorem rotationProjection_apply (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact)
    (x : S.X₁) (y : normalizedFreeRepresentation S.X₃) :
    (rotationProjection S hS).hom (x, y) = S.f.hom x + (presentationFreeLift S hS).hom y := rfl

theorem rotationInclusion_apply (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact)
    (x : normalizedSyzygy S.X₃) :
    (rotationInclusion S hS).hom x =
      ((presentationKernelMap S hS).hom x, -(kernel.ι (normalizedFreeAugmentation S.X₃)).hom x) := rfl

theorem rotation_zero (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    rotationInclusion S hS ≫ rotationProjection S hS = 0 := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  change S.f.hom ((presentationKernelMap S hS).hom x) +
    (presentationFreeLift S hS).hom (-(kernel.ι (normalizedFreeAugmentation S.X₃)).hom x) = 0
  have h := ConcreteCategory.congr_hom (presentationKernelMap_f S hS) x
  change S.f.hom ((presentationKernelMap S hS).hom x) =
    (presentationFreeLift S hS).hom ((kernel.ι (normalizedFreeAugmentation S.X₃)).hom x) at h
  rw [map_neg, h, add_neg_cancel]

def presentationRotation (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    ShortComplex (Rep.{0} ℤ G) :=
  ShortComplex.mk (rotationInclusion S hS) (rotationProjection S hS) (rotation_zero S hS)

theorem rotationProjection_g (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    rotationProjection S hS ≫ S.g = rotationSnd S ≫ normalizedFreeAugmentation S.X₃ := by
  rw [rotationProjection, Preadditive.add_comp, Category.assoc, S.zero, comp_zero,
    Category.assoc, presentationFreeLift_g, zero_add]

theorem rotationInclusion_injective (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    Function.Injective (rotationInclusion S hS).hom := by
  intro x y hxy
  apply (Rep.mono_iff_injective (kernel.ι (normalizedFreeAugmentation S.X₃))).mp inferInstance
  have h := congrArg Prod.snd hxy
  change -(kernel.ι (normalizedFreeAugmentation S.X₃)).hom x =
    -(kernel.ι (normalizedFreeAugmentation S.X₃)).hom y at h
  exact neg_injective h

theorem rotationProjection_surjective (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    Function.Surjective (rotationProjection S hS).hom := by
  intro z
  let y := normalizedFreeGenerator S.X₃ (S.g.hom z)
  have hy : S.g.hom ((presentationFreeLift S hS).hom y) = S.g.hom z :=
    (ConcreteCategory.congr_hom (presentationFreeLift_g S hS) y).trans
      (normalizedFreeAugmentation_generator _ _)
  have hz : S.g.hom (z - (presentationFreeLift S hS).hom y) = 0 := by
    rw [map_sub, hy, sub_self]
  obtain ⟨a, ha⟩ := (rep_shortComplex_exact_iff S).mp hS.exact _ hz
  refine ⟨(a, y), ?_⟩
  rw [rotationProjection_apply, ha, sub_add_cancel]

theorem presentationRotation_exact (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    (presentationRotation S hS).Exact := by
  apply (rep_shortComplex_exact_iff _).mpr
  intro z hz
  change rotationMiddle S at z
  change (rotationProjection S hS).hom z = 0 at hz
  have hc : (normalizedFreeAugmentation S.X₃).hom z.2 = 0 := by
    have h := ConcreteCategory.congr_hom (rotationProjection_g S hS) z
    change S.g.hom ((rotationProjection S hS).hom z) =
      (normalizedFreeAugmentation S.X₃).hom z.2 at h
    rw [hz, map_zero] at h
    exact h.symm
  obtain ⟨c, hc'⟩ := rep_kernel_element (normalizedFreeAugmentation S.X₃) z.2 hc
  have ha : z.1 = -(presentationKernelMap S hS).hom c := by
    apply (Rep.mono_iff_injective S.f).mp hS.mono_f
    have h := ConcreteCategory.congr_hom (presentationKernelMap_f S hS) c
    change S.f.hom ((presentationKernelMap S hS).hom c) =
      (presentationFreeLift S hS).hom ((kernel.ι (normalizedFreeAugmentation S.X₃)).hom c) at h
    change S.f.hom z.1 + (presentationFreeLift S hS).hom z.2 = 0 at hz
    rw [map_neg, h, hc']
    exact eq_neg_of_add_eq_zero_left hz
  refine ⟨-c, ?_⟩
  change (rotationInclusion S hS).hom (-c) = z
  rw [rotationInclusion_apply, map_neg, map_neg, neg_neg, hc']
  exact Prod.ext ha.symm rfl

theorem presentationRotation_shortExact (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    (presentationRotation S hS).ShortExact where
  exact := presentationRotation_exact S hS
  mono_f := (Rep.mono_iff_injective _).mpr (rotationInclusion_injective S hS)
  epi_g := (Rep.epi_iff_surjective _).mpr (rotationProjection_surjective S hS)

@[reassoc]
theorem rotationInclusion_fst (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    rotationInclusion S hS ≫ rotationFst S = presentationKernelMap S hS := rfl

@[reassoc]
theorem rotationInclusion_snd (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    rotationInclusion S hS ≫ rotationSnd S = -(kernel.ι (normalizedFreeAugmentation S.X₃)) := rfl

@[reassoc]
theorem rotationInl_fst (S : ShortComplex (Rep.{0} ℤ G)) :
    rotationInl S ≫ rotationFst S = 𝟙 S.X₁ := rfl

@[reassoc]
theorem rotationInl_projection (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    rotationInl S ≫ rotationProjection S hS = S.f := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  change S.f.hom x + (presentationFreeLift S hS).hom 0 = _
  rw [map_zero, add_zero]
  rfl

theorem rotation_fst_inl_stable (S : ShortComplex (Rep.{0} ℤ G)) :
    stableRepresentationClass _ _ (rotationFst S ≫ rotationInl S) =
      stableRepresentationClass _ _ (𝟙 (rotationMiddle S)) := by
  apply (stableRepresentationClass_eq_iff_projective_factor _ _).mpr
  refine ⟨normalizedFreeRepresentation S.X₃, inferInstance, -rotationSnd S, rotationInr S, ?_⟩
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  change (0, -x.2) = (x.1, 0) - x
  ext <;> simp

def rotationToNormalized (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    presentationRotation S hS ⟶ normalizedSyzygySequence S.X₃ where
  τ₁ := -𝟙 (normalizedSyzygy S.X₃)
  τ₂ := rotationSnd S
  τ₃ := S.g
  comm₁₂ := by
    change (-𝟙 _) ≫ kernel.ι _ = rotationInclusion S hS ≫ rotationSnd S
    rw [Preadditive.neg_comp, Category.id_comp, rotationInclusion_snd]
  comm₂₃ := (rotationProjection_g S hS).symm

end PolycyclicRecognition

end

end OAI
