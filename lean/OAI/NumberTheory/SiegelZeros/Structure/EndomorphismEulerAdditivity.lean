import Mathlib.Algebra.Module.SnakeLemma
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.Length

namespace OAI

namespace SiegelZeros


namespace WeightedTorusJets.EndomorphismEuler

section InducedMaps

variable {A M N : Type*} [CommRing A]
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]

def kernelMap (u : M →ₗ[A] M) (v : N →ₗ[A] N) (f : M →ₗ[A] N)
    (comm : f.comp u = v.comp f) : LinearMap.ker u →ₗ[A] LinearMap.ker v :=
  (f.domRestrict (LinearMap.ker u)).codRestrict (LinearMap.ker v) (by
    intro x
    change v (f x) = 0
    rw [← show f (u x) = v (f x) from DFunLike.congr_fun comm (x : M),
      show u x = 0 from x.property, map_zero])

@[simp] theorem kernelMap_apply (u : M →ₗ[A] M) (v : N →ₗ[A] N)
    (f : M →ₗ[A] N) (comm : f.comp u = v.comp f) (x : LinearMap.ker u) :
    (kernelMap u v f comm x : N) = f x := rfl

theorem kernelMap_injective (u : M →ₗ[A] M) (v : N →ₗ[A] N)
    (f : M →ₗ[A] N) (comm : f.comp u = v.comp f) (hf : Function.Injective f) :
    Function.Injective (kernelMap u v f comm) := by
  intro x y h
  apply Subtype.ext
  apply hf
  exact congrArg Subtype.val h

def cokernelMap (u : M →ₗ[A] M) (v : N →ₗ[A] N) (f : M →ₗ[A] N)
    (comm : f.comp u = v.comp f) :
    (M ⧸ LinearMap.range u) →ₗ[A] (N ⧸ LinearMap.range v) :=
  Submodule.mapQ (LinearMap.range u) (LinearMap.range v) f (by
    rintro x ⟨y, rfl⟩
    exact ⟨f y, (DFunLike.congr_fun comm y).symm⟩)

@[simp] theorem cokernelMap_mk (u : M →ₗ[A] M) (v : N →ₗ[A] N)
    (f : M →ₗ[A] N) (comm : f.comp u = v.comp f) (x : M) :
    cokernelMap u v f comm ((LinearMap.range u).mkQ x) =
      (LinearMap.range v).mkQ (f x) := rfl

theorem cokernelMap_surjective (u : M →ₗ[A] M) (v : N →ₗ[A] N)
    (f : M →ₗ[A] N) (comm : f.comp u = v.comp f) (hf : Function.Surjective f) :
    Function.Surjective (cokernelMap u v f comm) := by
  intro y
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range v) y
  obtain ⟨x, rfl⟩ := hf y
  exact ⟨(LinearMap.range u).mkQ x, rfl⟩

end InducedMaps

section ActualSnake

variable {A M₁ M₂ M₃ : Type*} [CommRing A]
  [AddCommGroup M₁] [Module A M₁] [AddCommGroup M₂] [Module A M₂]
  [AddCommGroup M₃] [Module A M₃]

variable (u₁ : M₁ →ₗ[A] M₁) (u₂ : M₂ →ₗ[A] M₂) (u₃ : M₃ →ₗ[A] M₃)
  (f : M₁ →ₗ[A] M₂) (g : M₂ →ₗ[A] M₃) (hExact : Function.Exact f g)
  (hleft : f.comp u₁ = u₂.comp f) (hright : g.comp u₂ = u₃.comp g)
  (hf : Function.Injective f) (hg : Function.Surjective g)

include hExact hf in

theorem kernelMap_exact :
    Function.Exact (kernelMap u₁ u₂ f hleft) (kernelMap u₂ u₃ g hright) := by
  intro x
  constructor
  · intro hx
    have hgx : g x = 0 := congrArg Subtype.val hx
    obtain ⟨y, hy⟩ := (hExact x).mp hgx
    have huy : u₁ y = 0 := by
      apply hf
      calc
        f (u₁ y) = u₂ (f y) := DFunLike.congr_fun hleft y
        _ = 0 := by rw [hy]; exact x.property
        _ = f 0 := (map_zero f).symm
    exact ⟨⟨y, huy⟩, Subtype.ext hy⟩
  · rintro ⟨y, rfl⟩
    apply Subtype.ext
    exact hExact.apply_apply_eq_zero (y : M₁)

include hExact hg in

theorem cokernelMap_exact :
    Function.Exact (cokernelMap u₁ u₂ f hleft) (cokernelMap u₂ u₃ g hright) := by
  intro x
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range u₂) x
  constructor
  · intro hx
    change (LinearMap.range u₃).mkQ (g x) = 0 at hx
    have hmem : g x ∈ LinearMap.range u₃ := (Submodule.Quotient.mk_eq_zero (LinearMap.range u₃)).mp hx
    obtain ⟨z, hz⟩ := hmem
    obtain ⟨y, hy⟩ := hg z
    have hxy : g (x - u₂ y) = 0 := by
      rw [map_sub, show g (u₂ y) = u₃ (g y) from DFunLike.congr_fun hright y,
        hy, hz, sub_self]
    obtain ⟨w, hw⟩ := (hExact (x - u₂ y)).mp hxy
    refine ⟨(LinearMap.range u₁).mkQ w, ?_⟩
    change (LinearMap.range u₂).mkQ (f w) = (LinearMap.range u₂).mkQ x
    rw [hw, map_sub]
    have hz₂ : (LinearMap.range u₂).mkQ (u₂ y) = 0 :=
      (Submodule.Quotient.mk_eq_zero (LinearMap.range u₂)).mpr ⟨y, rfl⟩
    rw [hz₂, sub_zero]
  · rintro ⟨y, hy⟩
    rw [← hy]
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range u₁) y
    change (LinearMap.range u₃).mkQ (g (f y)) = 0
    rw [hExact.apply_apply_eq_zero, map_zero]

noncomputable def connecting :
    LinearMap.ker u₃ →ₗ[A] (M₁ ⧸ LinearMap.range u₁) :=
  SnakeLemma.δ' u₁ u₂ u₃ f g hExact f g hExact hleft hright
    (LinearMap.ker u₃).subtype (LinearMap.exact_subtype_ker_map u₃)
    (LinearMap.range u₁).mkQ (LinearMap.exact_map_mkQ_range u₁) hg hf

theorem exact_kernel_connecting :
    Function.Exact (kernelMap u₂ u₃ g hright)
      (connecting u₁ u₂ u₃ f g hExact hleft hright hf hg) := by
  exact SnakeLemma.exact_δ'_right
    (i₁ := u₁) (i₂ := u₂) (i₃ := u₃)
    (f₁ := f) (f₂ := g) (hf := hExact) (g₁ := f) (g₂ := g) (hg := hExact)
    (h₁ := hleft) (h₂ := hright)
    (ι₂ := (LinearMap.ker u₂).subtype) (hι₂ := LinearMap.exact_subtype_ker_map u₂)
    (ι₃ := (LinearMap.ker u₃).subtype) (hι₃ := LinearMap.exact_subtype_ker_map u₃)
    (π₁ := (LinearMap.range u₁).mkQ) (hπ₁ := LinearMap.exact_map_mkQ_range u₁)
    hg hf (kernelMap u₂ u₃ g hright) (by ext x; rfl)
    (Submodule.subtype_injective _)

theorem exact_connecting_cokernel :
    Function.Exact (connecting u₁ u₂ u₃ f g hExact hleft hright hf hg)
      (cokernelMap u₁ u₂ f hleft) := by
  exact SnakeLemma.exact_δ'_left
    (i₁ := u₁) (i₂ := u₂) (i₃ := u₃)
    (f₁ := f) (f₂ := g) (hf := hExact) (g₁ := f) (g₂ := g) (hg := hExact)
    (h₁ := hleft) (h₂ := hright)
    (ι₃ := (LinearMap.ker u₃).subtype) (hι₃ := LinearMap.exact_subtype_ker_map u₃)
    (π₁ := (LinearMap.range u₁).mkQ) (hπ₁ := LinearMap.exact_map_mkQ_range u₁)
    (π₂ := (LinearMap.range u₂).mkQ) (hπ₂ := LinearMap.exact_map_mkQ_range u₂)
    hg hf (cokernelMap u₁ u₂ f hleft) (by ext x; rfl)
    (Submodule.mkQ_surjective _)

end ActualSnake

section LengthAlgebra

variable {A M N : Type*} [CommRing A]
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]

theorem length_eq_kernel_add_range (f : M →ₗ[A] N) :
    Module.length A M = Module.length A (LinearMap.ker f) +
      Module.length A (LinearMap.range f) := by
  calc
    Module.length A M = Module.length A (LinearMap.ker f) +
        Module.length A (M ⧸ LinearMap.ker f) :=
      Module.length_eq_add_of_exact (LinearMap.ker f).subtype (LinearMap.ker f).mkQ
        (Submodule.subtype_injective _) (Submodule.mkQ_surjective _)
        (LinearMap.exact_subtype_mkQ _)
    _ = _ := by rw [(LinearMap.quotKerEquivRange f).length_eq]

end LengthAlgebra

section SixTerm

variable {A X₁ X₂ X₃ X₄ X₅ X₆ : Type*} [CommRing A]
  [AddCommGroup X₁] [Module A X₁] [AddCommGroup X₂] [Module A X₂]
  [AddCommGroup X₃] [Module A X₃] [AddCommGroup X₄] [Module A X₄]
  [AddCommGroup X₅] [Module A X₅] [AddCommGroup X₆] [Module A X₆]

theorem six_term_length_cross_add
    (a : X₁ →ₗ[A] X₂) (b : X₂ →ₗ[A] X₃) (c : X₃ →ₗ[A] X₄)
    (d : X₄ →ₗ[A] X₅) (e : X₅ →ₗ[A] X₆)
    (ha : Function.Injective a) (he : Function.Surjective e)
    (hab : Function.Exact a b) (hbc : Function.Exact b c)
    (hcd : Function.Exact c d) (hde : Function.Exact d e) :
    Module.length A X₅ + Module.length A X₁ + Module.length A X₃ =
      Module.length A X₂ + Module.length A X₄ + Module.length A X₆ := by
  have h₁ : Module.length A X₁ = Module.length A (LinearMap.range a) :=
    (LinearEquiv.ofInjective a ha).length_eq
  have h₂ : Module.length A X₂ = Module.length A (LinearMap.range a) +
      Module.length A (LinearMap.range b) := by
    rw [length_eq_kernel_add_range b, ← LinearMap.exact_iff.mp hab]
  have h₃ : Module.length A X₃ = Module.length A (LinearMap.range b) +
      Module.length A (LinearMap.range c) := by
    rw [length_eq_kernel_add_range c, ← LinearMap.exact_iff.mp hbc]
  have h₄ : Module.length A X₄ = Module.length A (LinearMap.range c) +
      Module.length A (LinearMap.range d) := by
    rw [length_eq_kernel_add_range d, ← LinearMap.exact_iff.mp hcd]
  have h₅ : Module.length A X₅ = Module.length A (LinearMap.range d) +
      Module.length A (LinearMap.range e) := by
    rw [length_eq_kernel_add_range e, ← LinearMap.exact_iff.mp hde]
  have h₆ : Module.length A (LinearMap.range e) = Module.length A X₆ := by
    rw [LinearMap.range_eq_top.mpr he]
    exact Module.length_top
  rw [h₁, h₂, h₃, h₄, h₅, ← h₆]
  ac_rfl

end SixTerm


variable {A M₁ M₂ M₃ : Type*} [CommRing A]
  [AddCommGroup M₁] [Module A M₁] [AddCommGroup M₂] [Module A M₂]
  [AddCommGroup M₃] [Module A M₃]

theorem endomorphism_euler_cross_add
    (u₁ : M₁ →ₗ[A] M₁) (u₂ : M₂ →ₗ[A] M₂) (u₃ : M₃ →ₗ[A] M₃)
    (f : M₁ →ₗ[A] M₂) (g : M₂ →ₗ[A] M₃) (hExact : Function.Exact f g)
    (hleft : f.comp u₁ = u₂.comp f) (hright : g.comp u₂ = u₃.comp g)
    (hf : Function.Injective f) (hg : Function.Surjective g) :
    Module.length A (M₂ ⧸ LinearMap.range u₂) +
        Module.length A (LinearMap.ker u₁) + Module.length A (LinearMap.ker u₃) =
      Module.length A (LinearMap.ker u₂) + Module.length A (M₁ ⧸ LinearMap.range u₁) +
        Module.length A (M₃ ⧸ LinearMap.range u₃) := by
  exact six_term_length_cross_add
    (kernelMap u₁ u₂ f hleft) (kernelMap u₂ u₃ g hright)
    (connecting u₁ u₂ u₃ f g hExact hleft hright hf hg)
    (cokernelMap u₁ u₂ f hleft) (cokernelMap u₂ u₃ g hright)
    (kernelMap_injective u₁ u₂ f hleft hf) (cokernelMap_surjective u₂ u₃ g hright hg)
    (kernelMap_exact (u₁ := u₁) (u₂ := u₂) (u₃ := u₃) (f := f) (g := g)
      (hExact := hExact) (hleft := hleft) (hright := hright) (hf := hf))
    (exact_kernel_connecting u₁ u₂ u₃ f g hExact hleft hright hf hg)
    (exact_connecting_cokernel u₁ u₂ u₃ f g hExact hleft hright hf hg)
    (cokernelMap_exact (u₁ := u₁) (u₂ := u₂) (u₃ := u₃) (f := f) (g := g)
      (hExact := hExact) (hleft := hleft) (hright := hright) (hg := hg))


end WeightedTorusJets.EndomorphismEuler


end SiegelZeros

end OAI
