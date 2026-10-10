import Mathlib
import OAI.Analysis.WeakInfiniteness.AnnihilatorStates

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

open scoped ComplexOrder InnerProductSpace Topology

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

def selfAdjointMap (π : A →⋆ₐ[ℂ] B) : selfAdjoint A →L[ℝ] selfAdjoint B where
  toFun b := ⟨π (b : A),b.property.map π⟩
  map_add' _ _ := Subtype.ext (map_add π _ _)
  map_smul' r b := Subtype.ext (map_real_smul π (starHom_continuous π) r (b : A))
  cont := by
    have hπ : Continuous π := starHom_continuous π
    fun_prop

def realStatePullback (π : A →⋆ₐ[ℂ] B) (f : WeakDual ℝ (selfAdjoint B)) :
    WeakDual ℝ (selfAdjoint A) :=
  StrongDual.toWeakDual ((WeakDual.toStrongDual f).comp (selfAdjointMap π))

lemma realStatePullback_mem (π : A →⋆ₐ[ℂ] B) {f : WeakDual ℝ (selfAdjoint B)}
    (hf : f ∈ realStateSpace B) : realStatePullback π f ∈ realStateSpace A := by
  constructor
  · apply ((WeakDual.toStrongDual f).comp (selfAdjointMap π)).opNorm_le_bound zero_le_one
    intro b
    change ‖f (selfAdjointMap π b)‖ ≤ 1*‖b‖
    calc
      _ ≤ ‖WeakDual.toStrongDual f‖*‖selfAdjointMap π b‖ :=
        (WeakDual.toStrongDual f).le_opNorm _
      _ ≤ 1*‖selfAdjointMap π b‖ := mul_le_mul_of_nonneg_right hf.1 (norm_nonneg _)
      _ ≤ 1*‖b‖ := by
        gcongr
        exact NonUnitalStarAlgHom.norm_apply_le π.toNonUnitalStarAlgHom (b : A)
  · change f (selfAdjointMap π 1)=1
    have h1 : selfAdjointMap π 1=1 := Subtype.ext (map_one π)
    rw [h1]
    exact hf.2

variable [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]

omit [PartialOrder B] [StarOrderedRing B] in
lemma realStatePullback_annihilator (π : A →⋆ₐ[ℂ] B) {f : WeakDual ℝ (selfAdjoint B)}
    (hf : f ∈ realStateSpace B) (S : Set A) (hS : ∀ x ∈ S,π x=0) :
    realStatePullback π f ∈ annihilatorStates S := by
  refine ⟨realStatePullback_mem π hf,?_⟩
  intro x hx a
  change f (selfAdjointMap π ⟨star (x*a)*(x*a),(star_mul_self_nonneg (x*a)).isSelfAdjoint⟩)=0
  have hz : selfAdjointMap π ⟨star (x*a)*(x*a),(star_mul_self_nonneg (x*a)).isSelfAdjoint⟩=0 := by
    apply Subtype.ext
    change π (star (x*a)*(x*a))=0
    simp [map_mul,map_star,hS x hx]
  rw [hz,map_zero]

lemma exists_annihilator_norming_pullback [Nontrivial B] (π : A →⋆ₐ[ℂ] B)
    (S : Set A) (hS : ∀ x ∈ S,π x=0) (b : A) (hb : 0 ≤ b) :
    ∃ f ∈ annihilatorStates S,f ⟨b,hb.isSelfAdjoint⟩=‖π b‖ := by
  obtain ⟨g,hg,hgb⟩ := exists_norming_real_state (π b) (map_nonneg π hb)
  refine ⟨realStatePullback π g,realStatePullback_annihilator π hg S hS,?_⟩
  exact hgb

end

end WeakPureInfiniteness
end

end OAI
