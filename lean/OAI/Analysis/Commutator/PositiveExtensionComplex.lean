import Mathlib
import OAI.Analysis.Commutator.PositiveExtensionReal

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder

namespace Kadison.PositiveExtension

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def saInclusion (S : Submodule ℂ A) : saSubmodule S →ₗ[ℝ] S where
  toFun x := ⟨((x : selfAdjoint A) : A),x.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma positive_selfAdjoint_im (S : Submodule ℂ A) (h1 : (1 : A) ∈ S)
    (f : S →ₗ[ℂ] ℂ) (hf : ∀ x : S, 0 ≤ (x : A) → 0 ≤ f x)
    (x : saSubmodule S) : (f (saInclusion S x)).im=0 := by
  let u : S := ⟨1,h1⟩
  have hu : (f u).im=0 := (hf u zero_le_one).2.symm
  have hb : 0 ≤ ((‖x‖ • u-saInclusion S x : S) : A) := by
    change 0 ≤ ‖x‖ • (1 : A) - ((x : selfAdjoint A) : A)
    rw [sub_nonneg,←Algebra.algebraMap_eq_smul_one]
    exact (x : selfAdjoint A).property.le_algebraMap_norm_self
  have hi := (hf (‖x‖ • u-saInclusion S x) hb).2
  rw [map_sub,← Complex.coe_smul,map_smul] at hi
  simpa [smul_eq_mul,hu] using hi

def realRestriction (S : Submodule ℂ A) (f : S →ₗ[ℂ] ℂ) : saSubmodule S →ₗ[ℝ] ℝ :=
  Complex.reCLM.toLinearMap.comp ((f.restrictScalars ℝ).comp (saInclusion S))

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] lemma realRestriction_apply (S : Submodule ℂ A) (f : S →ₗ[ℂ] ℂ) (x) :
    realRestriction S f x=(f (saInclusion S x)).re := rfl

def complexify (g : selfAdjoint A →ₗ[ℝ] ℝ) : A →ₗ[ℂ] ℂ :=
  Module.Dual.extendRCLike (g.comp realPart)

omit [PartialOrder A] [StarOrderedRing A] in
lemma complexify_apply (g : selfAdjoint A →ₗ[ℝ] ℝ) (x : A) :
    complexify g x=(g (realPart x) : ℂ)+Complex.I*(g (imaginaryPart x) : ℂ) := by
  simp [complexify,Module.Dual.extendRCLike_apply,sub_eq_add_neg]

omit [PartialOrder A] [StarOrderedRing A] in
lemma complexify_selfAdjoint (g : selfAdjoint A →ₗ[ℝ] ℝ) (x : selfAdjoint A) :
    complexify g (x : A)=(g x : ℂ) := by simp [complexify_apply]

lemma complexify_nonneg (g : selfAdjoint A →ₗ[ℝ] ℝ)
    (hg : ∀ x : selfAdjoint A, 0 ≤ (x : A) → 0 ≤ g x) (a : A) (ha : 0 ≤ a) :
    0 ≤ complexify g a := by
  let x : selfAdjoint A := ⟨a,IsSelfAdjoint.of_nonneg ha⟩
  change 0 ≤ complexify g (x : A)
  rw [complexify_selfAdjoint]
  exact_mod_cast hg x ha

def complexifyPositive (g : selfAdjoint A →ₗ[ℝ] ℝ)
    (hg : ∀ x : selfAdjoint A, 0 ≤ (x : A) → 0 ≤ g x) : A →ₚ[ℂ] ℂ where
  toLinearMap := complexify g
  monotone' := by
    intro a b hab
    change complexify g a ≤ complexify g b
    have hh := complexify_nonneg g hg (b-a) (sub_nonneg.mpr hab)
    rw [map_sub] at hh
    exact sub_nonneg.mp hh

omit [PartialOrder A] [StarOrderedRing A] in
lemma realPart_mem (S : Submodule ℂ A) (hs : ∀ a ∈ S, star a ∈ S) (a : S) :
    (realPart (a : A) : A) ∈ S := by
  rw [realPart_apply_coe,←Complex.coe_smul]
  exact S.smul_mem _ (S.add_mem a.property (hs a a.property))

omit [PartialOrder A] [StarOrderedRing A] in
lemma imaginaryPart_mem (S : Submodule ℂ A) (hs : ∀ a ∈ S, star a ∈ S) (a : S) :
    (imaginaryPart (a : A) : A) ∈ S := by
  rw [imaginaryPart_apply_coe,←Complex.coe_smul]
  exact S.smul_mem _ (S.smul_mem _ (S.sub_mem a.property (hs a a.property)))

theorem exists_positive_extension (S : Submodule ℂ A) (h1 : (1 : A) ∈ S)
    (hs : ∀ a ∈ S, star a ∈ S) (f : S →ₗ[ℂ] ℂ)
    (hf : ∀ x : S, 0 ≤ (x : A) → 0 ≤ f x) :
    ∃ g : A →ₚ[ℂ] ℂ, ∀ x : S, g x=f x := by
  obtain ⟨g,hg,hgp⟩ := exists_real_extension S h1 (realRestriction S f) (by
    intro x hx
    exact (hf (saInclusion S x) hx).1)
  refine ⟨complexifyPositive g.toLinearMap hgp,?_⟩
  intro x
  let xr : saSubmodule S := ⟨realPart (x : A),realPart_mem S hs x⟩
  let xi : saSubmodule S := ⟨imaginaryPart (x : A),imaginaryPart_mem S hs x⟩
  have hxr : ((f (saInclusion S xr)).re : ℂ)=f (saInclusion S xr) := by
    exact Complex.ext (by simp) (by simp [positive_selfAdjoint_im S h1 f hf xr])
  have hxi : ((f (saInclusion S xi)).re : ℂ)=f (saInclusion S xi) := by
    exact Complex.ext (by simp) (by simp [positive_selfAdjoint_im S h1 f hf xi])
  have hd : saInclusion S xr+Complex.I • saInclusion S xi=x := by
    apply Subtype.ext
    exact realPart_add_I_smul_imaginaryPart (x : A)
  change complexify g.toLinearMap (x : A)=f x
  rw [complexify_apply]
  change (g (xr : selfAdjoint A) : ℂ)+Complex.I*(g (xi : selfAdjoint A) : ℂ)=f x
  rw [hg xr,hg xi,realRestriction_apply,realRestriction_apply,hxr,hxi,←smul_eq_mul,
    ←map_smul,←map_add,hd]

end Kadison.PositiveExtension

end

end
end

end OAI
