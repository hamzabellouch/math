import Mathlib
import OAI.Analysis.WeakInfiniteness.TensorFoundations

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate

namespace WeakPureInfiniteness

universe u v

section AlgebraicSpan

variable {A : Type*} [NonUnitalCStarAlgebra A]

def linearStarSpan (S : Set A) (hm : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S)
    (hs : ∀ x ∈ S, star x ∈ S) : NonUnitalStarSubalgebra ℂ A where
  carrier := Submodule.span ℂ S
  zero_mem' := Submodule.zero_mem _
  add_mem' := Submodule.add_mem _
  smul_mem' c _ hx := Submodule.smul_mem _ c hx
  mul_mem' {a} {b} ha hb := by
    change a * b ∈ Submodule.span ℂ S
    induction ha using Submodule.span_induction with
    | mem x hx =>
      induction hb using Submodule.span_induction with
      | mem y hy => exact Submodule.subset_span (hm x hx y hy)
      | zero => simp
      | add x y _ _ hpx hpy => rw [mul_add]; exact Submodule.add_mem _ hpx hpy
      | smul c x _ hpx => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hpx
    | zero => simp
    | add x y _ _ hpx hpy => rw [add_mul]; exact Submodule.add_mem _ hpx hpy
    | smul c x _ hpx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hpx
  star_mem' {a} ha := by
    change star a ∈ Submodule.span ℂ S
    induction ha using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (hs x hx)
    | zero => simp
    | add x y _ _ hpx hpy => rw [star_add]; exact Submodule.add_mem _ hpx hpy
    | smul c x _ hpx => rw [star_smul]; exact Submodule.smul_mem _ (star c) hpx

lemma linearStarSpan_eq_adjoin (S : Set A) (hm : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S)
    (hs : ∀ x ∈ S, star x ∈ S) :
    linearStarSpan S hm hs = NonUnitalStarAlgebra.adjoin ℂ S := by
  apply le_antisymm
  · change Submodule.span ℂ S ≤ (NonUnitalStarAlgebra.adjoin ℂ S).toNonUnitalSubalgebra.toSubmodule
    exact Submodule.span_le.mpr (NonUnitalStarAlgebra.subset_adjoin ℂ S)
  · exact NonUnitalStarAlgebra.adjoin_le (fun _ hx => Submodule.subset_span hx)

lemma closure_adjoin_eq_closure_span (S : Set A) (hm : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S)
    (hs : ∀ x ∈ S, star x ∈ S) :
    closure (NonUnitalStarAlgebra.adjoin ℂ S : Set A) =
      closure (Submodule.span ℂ S : Set A) := by
  rw [← linearStarSpan_eq_adjoin S hm hs]
  rfl

end AlgebraicSpan

section TensorSpan

variable {A : Type u} {B C : Type v} [NonUnitalCStarAlgebra A]
  [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]

lemma minimalTensor_eq_closure_span :
    (minimalTensorSubalgebra A B : Set (SpatialAmbient A B)) =
      closure (Submodule.span ℂ (Set.range fun p : A × B => spatialElementary p.1 p.2) : Set (SpatialAmbient A B)) := by
  apply closure_adjoin_eq_closure_span
  · rintro _ ⟨⟨a,b⟩,rfl⟩ _ ⟨⟨c,d⟩,rfl⟩
    exact ⟨(a*c,b*d), spatialElementary_mul a c b d⟩
  · rintro _ ⟨⟨a,b⟩,rfl⟩
    exact ⟨(star a, star b), spatialElementary_star a b⟩

lemma tensorKernelIdeal_eq_closure_span (q : B →⋆ₙₐ[ℂ] C) :
    (tensorKernelIdeal (A := A) q : Set (SpatialAmbient A B)) =
      closure (Submodule.span ℂ {z | ∃ a : A, ∃ b : B, q b = 0 ∧ z = spatialElementary a b} :
        Set (SpatialAmbient A B)) := by
  apply closure_adjoin_eq_closure_span
  · rintro _ ⟨a,b,hb,rfl⟩ _ ⟨c,d,hd,rfl⟩
    exact ⟨a*c,b*d,by rw [map_mul,hb,zero_mul], (spatialElementary_mul a c b d).symm⟩
  · rintro _ ⟨a,b,hb,rfl⟩
    exact ⟨star a,star b,by rw [map_star,hb,star_zero], (spatialElementary_star a b).symm⟩

end TensorSpan

end WeakPureInfiniteness
end

end OAI
