import OAI.GroupTheory.PolycyclicRecognition.Analysis.HorseshoeCover

namespace OAI

/-! # Exactness of the kernel sequence of the endpoint free covers -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

theorem horseshoeKernel_zero (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    horseshoeKernelInl S hS ≫ horseshoeKernelSnd S hS = 0 := by
  apply (cancel_mono (kernel.ι (normalizedFreeAugmentation S.X₃))).mp
  rw [Category.assoc, horseshoeKernelSnd_ι, ← Category.assoc, horseshoeKernelInl_ι]
  have h : horseshoeInl S ≫ horseshoeSnd S = 0 := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    rfl
  rw [Category.assoc, h, comp_zero, zero_comp]

def horseshoeSyzygySequence (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    ShortComplex (Rep.{0} ℤ G) :=
  ShortComplex.mk (horseshoeKernelInl S hS) (horseshoeKernelSnd S hS) (horseshoeKernel_zero S hS)

theorem horseshoeKernelInl_injective (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    Function.Injective (horseshoeKernelInl S hS).hom := by
  intro x y hxy
  apply (Rep.mono_iff_injective (kernel.ι (normalizedFreeAugmentation S.X₁))).mp inferInstance
  have h := congrArg (fun z => (kernel.ι (horseshoeAugmentation S hS)).hom z) hxy
  rw [horseshoeKernelInl_apply, horseshoeKernelInl_apply] at h
  exact congrArg Prod.fst h

theorem horseshoeSyzygySequence_exact (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    (horseshoeSyzygySequence S hS).Exact := by
  apply (rep_shortComplex_exact_iff _).mpr
  intro x hx
  change horseshoeKernel S hS at x
  change (horseshoeKernelSnd S hS).hom x = 0 at hx
  have hsnd : ((kernel.ι (horseshoeAugmentation S hS)).hom x).2 = 0 := by
    rw [← horseshoeKernelSnd_apply, hx, map_zero]
  have hfst : (normalizedFreeAugmentation S.X₁).hom
      ((kernel.ι (horseshoeAugmentation S hS)).hom x).1 = 0 := by
    apply (Rep.mono_iff_injective S.f).mp hS.mono_f
    have h := horseshoeKernel_condition S hS x
    rw [hsnd, map_zero, add_zero] at h
    simpa only [map_zero] using h
  obtain ⟨y, hy⟩ := rep_kernel_element (normalizedFreeAugmentation S.X₁) _ hfst
  refine ⟨y, ?_⟩
  change (horseshoeKernelInl S hS).hom y = x
  apply (Rep.mono_iff_injective (kernel.ι (horseshoeAugmentation S hS))).mp inferInstance
  rw [horseshoeKernelInl_apply, hy]
  exact Prod.ext rfl hsnd.symm

theorem horseshoeKernelSnd_surjective (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    Function.Surjective (horseshoeKernelSnd S hS).hom := by
  intro y
  let c := (kernel.ι (normalizedFreeAugmentation S.X₃)).hom y
  have hc : (normalizedFreeAugmentation S.X₃).hom c = 0 :=
    ConcreteCategory.congr_hom (kernel.condition (normalizedFreeAugmentation S.X₃)) y
  have hl : S.g.hom ((presentationFreeLift S hS).hom c) = 0 := by
    exact (ConcreteCategory.congr_hom (presentationFreeLift_g S hS) c).trans hc
  obtain ⟨a, ha⟩ := (rep_shortComplex_exact_iff S).mp hS.exact
    (- (presentationFreeLift S hS).hom c) (by rw [map_neg, hl, neg_zero])
  let u : horseshoeCover S := (normalizedFreeGenerator S.X₁ a, c)
  have hu : (horseshoeAugmentation S hS).hom u = 0 := by
    rw [horseshoeAugmentation_apply, normalizedFreeAugmentation_generator, ha, neg_add_cancel]
  obtain ⟨x, hx⟩ := rep_kernel_element (horseshoeAugmentation S hS) u hu
  refine ⟨x, ?_⟩
  apply (Rep.mono_iff_injective (kernel.ι (normalizedFreeAugmentation S.X₃))).mp inferInstance
  rw [horseshoeKernelSnd_apply, hx]

theorem horseshoeSyzygySequence_shortExact (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    (horseshoeSyzygySequence S hS).ShortExact where
  exact := horseshoeSyzygySequence_exact S hS
  mono_f := (Rep.mono_iff_injective _).mpr (horseshoeKernelInl_injective S hS)
  epi_g := (Rep.epi_iff_surjective _).mpr (horseshoeKernelSnd_surjective S hS)

end PolycyclicRecognition

end

end OAI
