import OAI.GroupTheory.PolycyclicRecognition.Algebra.PresentationKernelMap
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RepCofiber

namespace OAI

/-! # A projective cover adapted to a short exact coefficient sequence

The middle cover is the product of the two endpoint free covers. Its kernel
will provide an exact sequence of syzygies, without claiming that the
normalized free-cover functor itself is exact.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

theorem rep_kernel_element {A B : Rep.{0} ℤ G} (f : A ⟶ B) (x : A)
    (hx : f.hom x = 0) : ∃ y : (kernel f : Rep.{0} ℤ G), (kernel.ι f).hom y = x :=
  (rep_shortComplex_exact_iff (ShortComplex.mk (kernel.ι f) f (kernel.condition f))).mp
    (ShortComplex.exact_kernel f) x hx

abbrev horseshoeCover (S : ShortComplex (Rep.{0} ℤ G)) : Rep.{0} ℤ G :=
  Rep.of ((normalizedFreeRepresentation S.X₁).ρ.prod (normalizedFreeRepresentation S.X₃).ρ)

def horseshoeFst (S : ShortComplex (Rep.{0} ℤ G)) :
    horseshoeCover S ⟶ normalizedFreeRepresentation S.X₁ :=
  Rep.ofHom (.fst ℤ _ _)

def horseshoeSnd (S : ShortComplex (Rep.{0} ℤ G)) :
    horseshoeCover S ⟶ normalizedFreeRepresentation S.X₃ :=
  Rep.ofHom (.snd ℤ _ _)

def horseshoeInl (S : ShortComplex (Rep.{0} ℤ G)) :
    normalizedFreeRepresentation S.X₁ ⟶ horseshoeCover S :=
  Rep.ofHom (.inl ℤ _ _)

def horseshoeInr (S : ShortComplex (Rep.{0} ℤ G)) :
    normalizedFreeRepresentation S.X₃ ⟶ horseshoeCover S :=
  Rep.ofHom (.inr ℤ _ _)

theorem horseshoe_total (S : ShortComplex (Rep.{0} ℤ G)) :
    horseshoeFst S ≫ horseshoeInl S + horseshoeSnd S ≫ horseshoeInr S = 𝟙 _ := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  change (x.1 + 0, 0 + x.2) = x
  simp only [add_zero, zero_add]

instance horseshoeCover_projective (S : ShortComplex (Rep.{0} ℤ G)) :
    Projective (horseshoeCover S) where
  factors f e _ := by
    let l := Projective.factorThru (horseshoeInl S ≫ f) e
    let r := Projective.factorThru (horseshoeInr S ≫ f) e
    refine ⟨horseshoeFst S ≫ l + horseshoeSnd S ≫ r, ?_⟩
    rw [Preadditive.add_comp, Category.assoc, Category.assoc,
      Projective.factorThru_comp, Projective.factorThru_comp,
      ← Category.assoc, ← Category.assoc, ← Preadditive.add_comp,
      horseshoe_total, Category.id_comp]

def horseshoeAugmentation (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    horseshoeCover S ⟶ S.X₂ :=
  horseshoeFst S ≫ normalizedFreeAugmentation S.X₁ ≫ S.f +
    horseshoeSnd S ≫ presentationFreeLift S hS

theorem horseshoeAugmentation_apply (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact)
    (x : normalizedFreeRepresentation S.X₁) (y : normalizedFreeRepresentation S.X₃) :
    (horseshoeAugmentation S hS).hom (x, y) =
      S.f.hom ((normalizedFreeAugmentation S.X₁).hom x) + (presentationFreeLift S hS).hom y := rfl

@[reassoc]
theorem horseshoeAugmentation_g (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    horseshoeAugmentation S hS ≫ S.g = horseshoeSnd S ≫ normalizedFreeAugmentation S.X₃ := by
  rw [horseshoeAugmentation, Preadditive.add_comp, Category.assoc, Category.assoc,
    S.zero, comp_zero, comp_zero, Category.assoc, presentationFreeLift_g, zero_add]

@[reassoc]
theorem horseshoeInl_augmentation (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    horseshoeInl S ≫ horseshoeAugmentation S hS = normalizedFreeAugmentation S.X₁ ≫ S.f := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  change S.f.hom ((normalizedFreeAugmentation S.X₁).hom x) +
    (presentationFreeLift S hS).hom 0 = _
  rw [map_zero, add_zero]
  rfl

theorem horseshoeAugmentation_surjective (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    Function.Surjective (horseshoeAugmentation S hS).hom := by
  intro z
  let y := normalizedFreeGenerator S.X₃ (S.g.hom z)
  have hy : S.g.hom ((presentationFreeLift S hS).hom y) = S.g.hom z := by
    have h := ConcreteCategory.congr_hom (presentationFreeLift_g S hS) y
    exact h.trans (normalizedFreeAugmentation_generator _ _)
  have hz : S.g.hom (z - (presentationFreeLift S hS).hom y) = 0 := by
    rw [map_sub, hy, sub_self]
  obtain ⟨a, ha⟩ := (rep_shortComplex_exact_iff S).mp hS.exact _ hz
  refine ⟨(normalizedFreeGenerator S.X₁ a, y), ?_⟩
  rw [horseshoeAugmentation_apply, normalizedFreeAugmentation_generator, ha, sub_add_cancel]

instance horseshoeAugmentation_epi (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    Epi (horseshoeAugmentation S hS) :=
  (Rep.epi_iff_surjective _).mpr (horseshoeAugmentation_surjective S hS)

abbrev horseshoeKernel (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) : Rep.{0} ℤ G :=
  kernel (horseshoeAugmentation S hS)

def horseshoeKernelInl (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    normalizedSyzygy S.X₁ ⟶ horseshoeKernel S hS :=
  kernel.lift (horseshoeAugmentation S hS)
    (kernel.ι (normalizedFreeAugmentation S.X₁) ≫ horseshoeInl S) (by
      rw [Category.assoc, horseshoeInl_augmentation, ← Category.assoc, kernel.condition, zero_comp])

@[reassoc]
theorem horseshoeKernelInl_ι (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    horseshoeKernelInl S hS ≫ kernel.ι (horseshoeAugmentation S hS) =
      kernel.ι (normalizedFreeAugmentation S.X₁) ≫ horseshoeInl S := kernel.lift_ι _ _ _

def horseshoeKernelSnd (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    horseshoeKernel S hS ⟶ normalizedSyzygy S.X₃ :=
  kernel.lift (normalizedFreeAugmentation S.X₃)
    (kernel.ι (horseshoeAugmentation S hS) ≫ horseshoeSnd S) (by
      rw [Category.assoc, ← horseshoeAugmentation_g S hS, ← Category.assoc,
        kernel.condition, zero_comp])

@[reassoc]
theorem horseshoeKernelSnd_ι (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    horseshoeKernelSnd S hS ≫ kernel.ι (normalizedFreeAugmentation S.X₃) =
      kernel.ι (horseshoeAugmentation S hS) ≫ horseshoeSnd S := kernel.lift_ι _ _ _

theorem horseshoeKernelInl_apply (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact)
    (x : normalizedSyzygy S.X₁) :
    (kernel.ι (horseshoeAugmentation S hS)).hom ((horseshoeKernelInl S hS).hom x) =
      ((kernel.ι (normalizedFreeAugmentation S.X₁)).hom x, 0) :=
  ConcreteCategory.congr_hom (horseshoeKernelInl_ι S hS) x

theorem horseshoeKernelSnd_apply (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact)
    (x : horseshoeKernel S hS) :
    (kernel.ι (normalizedFreeAugmentation S.X₃)).hom ((horseshoeKernelSnd S hS).hom x) =
      ((kernel.ι (horseshoeAugmentation S hS)).hom x).2 :=
  ConcreteCategory.congr_hom (horseshoeKernelSnd_ι S hS) x

theorem horseshoeKernel_condition (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact)
    (x : horseshoeKernel S hS) :
    S.f.hom ((normalizedFreeAugmentation S.X₁).hom
        ((kernel.ι (horseshoeAugmentation S hS)).hom x).1) +
      (presentationFreeLift S hS).hom ((kernel.ι (horseshoeAugmentation S hS)).hom x).2 = 0 :=
  ConcreteCategory.congr_hom (kernel.condition (horseshoeAugmentation S hS)) x

end PolycyclicRecognition

end

end OAI
