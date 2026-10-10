import Mathlib
import OAI.Analysis.WeakInfiniteness.CrossUniverseTensorMap
import OAI.Analysis.WeakInfiniteness.WordTensorDensity

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open TopologicalSpace

open scoped TensorProduct

universe u v

section Separable

variable {A : Type u} {B : Type v} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

instance minimalTensor_separable [SeparableSpace A] [SeparableSpace B] :
    SeparableSpace (MinimalTensor A B) := by
  let t : ℕ × ℕ → MinimalTensor A B := fun p => minimalElementary (denseSeq A p.1) (denseSeq B p.2)
  let S := Submodule.span ℂ (Set.range t)
  have hs : IsSeparable (S.topologicalClosure : Set (MinimalTensor A B)) :=
    ((Set.countable_range t).isSeparable.span (R := ℂ)).closure
  have hij : ∀ i j,minimalElementary (denseSeq A i) (denseSeq B j) ∈ S.topologicalClosure := by
    intro i j
    exact S.le_topologicalClosure (Submodule.subset_span ⟨(i,j),rfl⟩)
  have hib : ∀ i b,minimalElementary (denseSeq A i) b ∈ S.topologicalClosure := by
    intro i b
    have hc : IsClosed {b : B | minimalElementary (denseSeq A i) b ∈ S.topologicalClosure} :=
      S.isClosed_topologicalClosure.preimage (minimalElementaryRightContinuous (denseSeq A i)).continuous
    have hsub : Set.range (denseSeq B) ⊆ {b : B | minimalElementary (denseSeq A i) b ∈ S.topologicalClosure} := by
      rintro _ ⟨j,rfl⟩
      exact hij i j
    exact closure_minimal hsub hc (denseRange_denseSeq B b)
  have he : S.topologicalClosure=⊤ := by
    apply minimal_elementary_span_dense _ S.isClosed_topologicalClosure
    intro a b
    have hc : IsClosed {a : A | minimalElementary a b ∈ S.topologicalClosure} :=
      S.isClosed_topologicalClosure.preimage (minimalElementaryLeftContinuous b).continuous
    have hsub : Set.range (denseSeq A) ⊆ {a : A | minimalElementary a b ∈ S.topologicalClosure} := by
      rintro _ ⟨i,rfl⟩
      exact hib i b
    exact closure_minimal hsub hc (denseRange_denseSeq A a)
  rw [he] at hs
  exact isSeparable_univ_iff.mp hs

end Separable

section ElementaryZero

variable {A : Type u} {B : Type v} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

lemma minimalElementary_eq_zero_iff (a : A) (b : B) :
    minimalElementary a b=0 ↔ a=0 ∨ b=0 := by
  constructor
  · intro hab
    by_cases hb : b=0
    · exact Or.inr hb
    obtain ⟨H,π,hπ⟩ := exists_faithful_representation A
    obtain ⟨K,ρ,hρ⟩ := exists_faithful_representation B
    have hr : ρ b ≠ 0 := by
      intro hz
      exact hb (hρ (hz.trans (map_zero ρ).symm))
    obtain ⟨y,hy⟩ : ∃ y : K,ρ b y ≠ 0 := by
      by_contra hn
      push Not at hn
      exact hr (ContinuousLinearMap.ext hn)
    have hn : ‖TensorProduct.mapL (π a) (ρ b)‖ ≤ ‖minimalElementary a b‖ := by
      change ‖TensorProduct.mapL (π a) (ρ b)‖ ≤ ‖spatialElementary a b‖
      simpa using norm_tensorSum_le_spatial_any ({()} : Finset Unit) (fun _ : Unit => a)
        (fun _ : Unit => b) π ρ
    rw [hab,norm_zero] at hn
    have hp : π a=0 := by
      ext x
      have he := (TensorProduct.mapL (π a) (ρ b)).le_opNorm (x ⊗ₜ[ℂ] y)
      have hz : ‖(TensorProduct.mapL (π a) (ρ b)) (x ⊗ₜ[ℂ] y)‖ ≤ 0 := by
        calc
          _ ≤ ‖TensorProduct.mapL (π a) (ρ b)‖ * ‖x ⊗ₜ[ℂ] y‖ := he
          _ ≤ 0 * ‖x ⊗ₜ[ℂ] y‖ := mul_le_mul_of_nonneg_right hn (norm_nonneg _)
          _ = 0 := zero_mul _
      simp only [TensorProduct.mapL_tmul,TensorProduct.norm_tmul] at hz
      have hnorm : ‖(π a) x‖ * ‖(ρ b) y‖ = 0 :=
        le_antisymm hz (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      exact norm_eq_zero.mp ((mul_eq_zero.mp hnorm).resolve_right (norm_ne_zero_iff.mpr hy))
    exact Or.inl (hπ (hp.trans (map_zero π).symm))
  · rintro (rfl | rfl)
    · exact map_zero (minimalElementaryLeftLinear b)
    · exact map_zero (minimalElementaryRightLinear a)

end ElementaryZero

section LeftEmbedding

variable (A : Type u) (B : Type v) [NonUnitalCStarAlgebra A] [CStarAlgebra B]

def minimalLeftEmbedding : A →⋆ₙₐ[ℂ] MinimalTensor A B where
  toFun a := minimalElementary a 1
  map_zero' := map_zero (minimalElementaryLeftLinear (1:B))
  map_add' a b := map_add (minimalElementaryLeftLinear (1:B)) a b
  map_smul' c a := map_smul (minimalElementaryLeftLinear (1:B)) c a
  map_mul' a b := by rw [← minimalElementary_mul,one_mul]
  map_star' a := by rw [← minimalElementary_star,star_one]

lemma minimalLeftEmbedding_injective [Nontrivial B] : Function.Injective (minimalLeftEmbedding A B) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro a ha
  exact ((minimalElementary_eq_zero_iff a (1:B)).mp ha).resolve_right one_ne_zero

lemma minimalLeftEmbedding_isometry [Nontrivial B] : Isometry (minimalLeftEmbedding A B) :=
  NonUnitalStarAlgHom.isometry _ (minimalLeftEmbedding_injective A B)

end LeftEmbedding

end

end WeakPureInfiniteness
end

end OAI
