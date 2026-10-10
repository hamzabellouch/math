import Mathlib
import OAI.Analysis.WeakInfiniteness.FullGroupAlgebra
import OAI.Analysis.WeakInfiniteness.SmallCStar
import OAI.Analysis.WeakInfiniteness.States

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

open scoped ComplexOrder

universe u v

section Words

variable {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]

def cuntzWord (s : ℕ → A) : List (ℕ × Bool) → A
  | [] => 1
  | (i,b)::w => (if b then s i else star (s i))*cuntzWord s w

def cuntzPolynomial (s : ℕ → A) (c : List (ℕ × Bool) →₀ ℂ) : A :=
  c.sum fun w t => t • cuntzWord s w

lemma map_cuntzWord (φ : A →⋆ₐ[ℂ] B) (s : ℕ → A) (w : List (ℕ × Bool)) :
    φ (cuntzWord s w)=cuntzWord (fun i => φ (s i)) w := by
  induction w with
  | nil => exact map_one φ
  | cons i w ih => rcases i with ⟨i,b⟩; cases b <;> simp [cuntzWord,ih,map_star]

lemma map_cuntzPolynomial (φ : A →⋆ₐ[ℂ] B) (s : ℕ → A) (c : List (ℕ × Bool) →₀ ℂ) :
    φ (cuntzPolynomial s c)=cuntzPolynomial (fun i => φ (s i)) c := by
  simp [cuntzPolynomial,Finsupp.sum,map_cuntzWord]

lemma cuntzWord_append (s : ℕ → A) (w z : List (ℕ × Bool)) :
    cuntzWord s (w++z)=cuntzWord s w*cuntzWord s z := by
  induction w with
  | nil => simp [cuntzWord]
  | cons i w ih => simp [cuntzWord,ih,mul_assoc]

def cuntzWordMonoid (s : ℕ → A) : Submonoid A where
  carrier := Set.range (cuntzWord s)
  one_mem' := ⟨[],rfl⟩
  mul_mem' := by
    rintro _ _ ⟨w,rfl⟩ ⟨z,rfl⟩
    exact ⟨w++z,cuntzWord_append s w z⟩

lemma adjoin_le_cuntzWordSpan (s : ℕ → A) :
    (StarAlgebra.adjoin ℂ (Set.range s)).toSubalgebra.toSubmodule ≤
      Submodule.span ℂ (Set.range (cuntzWord s)) := by
  rw [StarAlgebra.adjoin_eq_span]
  apply Submodule.span_mono
  change Submonoid.closure (Set.range s ∪ star (Set.range s)) ≤ cuntzWordMonoid s
  apply Submonoid.closure_le.mpr
  intro y hy
  rcases hy with ⟨i,rfl⟩ | hy
  · exact ⟨[(i,true)],by simp [cuntzWord]⟩
  · obtain ⟨i,hi⟩ : ∃ i,s i=star y := hy
    exact ⟨[(i,false)],by simp [cuntzWord,hi]⟩

lemma exists_cuntzPolynomial_of_mem_adjoin (s : ℕ → A) (y : A)
    (hy : y ∈ StarAlgebra.adjoin ℂ (Set.range s)) :
    ∃ c : List (ℕ × Bool) →₀ ℂ,cuntzPolynomial s c=y :=
  Finsupp.mem_span_range_iff_exists_finsupp.mp (adjoin_le_cuntzWordSpan s hy)

lemma closedStarSpan_range_separable (s : ℕ → A) :
    SeparableSpace (closedStarSpan (Set.range s)) := by
  have hs := (Set.countable_range (cuntzWord s)).isSeparable.span (R := ℂ)
  have hsub : (StarAlgebra.adjoin ℂ (Set.range s) : Set A) ⊆
      (Submodule.span ℂ (Set.range (cuntzWord s)) : Set A) := adjoin_le_cuntzWordSpan s
  exact (hs.closure.mono (closure_mono hsub)).separableSpace

end Words

instance oInfinity_separable : SeparableSpace OInfinity :=
  closedStarSpan_range_separable cuntzGenerator

section NormBound

variable {A : Type u} [CStarAlgebra A]

lemma norm_cuntzPolynomial_small {B : Type} [CStarAlgebra B]
    [PartialOrder B] [StarOrderedRing B] (s : ℕ → B)
    (hs : ∀ i j,star (s i)*s j=if i=j then 1 else 0) (c : List (ℕ × Bool) →₀ ℂ) :
    ‖cuntzPolynomial s c‖ ≤ ‖cuntzPolynomial oInfinityIsometry c‖ := by
  by_cases hn : Nontrivial B
  · let := hn
    obtain ⟨f,hf,hfn⟩ := exists_norming_gns (cuntzPolynomial s c)
    have hv : gnsCyclicVector f ≠ 0 := by
      intro h
      have hh := norm_gnsCyclicVector f hf
      rw [h,norm_zero] at hh
      norm_num at hh
    let : Nontrivial f.GNS := ⟨⟨gnsCyclicVector f,0,hv⟩⟩
    let π : CuntzRepresentation :=
      { hilbert := { Carrier := f.GNS }
        generators := fun i => f.gnsStarAlgHom (s i)
        relations := fun i j => by
          rw [← map_star,← map_mul,hs i j]
          split_ifs <;> simp }
    calc
      ‖cuntzPolynomial s c‖ = ‖f.gnsStarAlgHom (cuntzPolynomial s c)‖ := hfn.symm
      _ = ‖oInfinityEvaluation π (cuntzPolynomial oInfinityIsometry c)‖ := by
        rw [map_cuntzPolynomial,map_cuntzPolynomial]
        rfl
      _ ≤ _ := NonUnitalStarAlgHom.norm_apply_le (oInfinityEvaluation π) _
  · let := not_nontrivial_iff_subsingleton.mp hn
    rw [Subsingleton.elim (cuntzPolynomial s c) 0,norm_zero]
    exact norm_nonneg _

lemma norm_cuntzPolynomial_separable [SeparableSpace A] (s : ℕ → A)
    (hs : ∀ i j,star (s i)*s j=if i=j then 1 else 0) (c : List (ℕ × Bool) →₀ ℂ) :
    ‖cuntzPolynomial s c‖ ≤ ‖cuntzPolynomial oInfinityIsometry c‖ := by
  let := small_of_separable_metric A
  let B := SmallCStarCarrier A
  let := CStarAlgebra.spectralOrder B
  let := CStarAlgebra.spectralOrderedRing B
  let e : B ≃⋆ₐ[ℂ] A := smallCStarStarAlgEquiv A
  let t : ℕ → B := fun i => e.symm (s i)
  have ht : ∀ i j,star (t i)*t j=if i=j then 1 else 0 := by
    intro i j
    dsimp [t]
    rw [← map_star,← map_mul,hs i j]
    split_ifs <;> simp
  have he : cuntzPolynomial s c=e (cuntzPolynomial t c) := by
    change cuntzPolynomial s c=e.toStarAlgHom (cuntzPolynomial t c)
    rw [map_cuntzPolynomial]
    change cuntzPolynomial s c=cuntzPolynomial (fun i => e (e.symm (s i))) c
    simp only [e.apply_symm_apply]
  rw [he,StarAlgEquiv.norm_map]
  exact norm_cuntzPolynomial_small t ht c

lemma norm_cuntzPolynomial_le (s : ℕ → A)
    (hs : ∀ i j,star (s i)*s j=if i=j then 1 else 0) (c : List (ℕ × Bool) →₀ ℂ) :
    ‖cuntzPolynomial s c‖ ≤ ‖cuntzPolynomial oInfinityIsometry c‖ := by
  let S := closedStarSpan (Set.range s)
  let : CStarAlgebra S := closedStarSpanCStar _
  let : SeparableSpace S := closedStarSpan_range_separable s
  let t : ℕ → S := fun i => ⟨s i,subset_closedStarSpan _ ⟨i,rfl⟩⟩
  have ht : ∀ i j,star (t i)*t j=if i=j then 1 else 0 := by
    intro i j
    apply Subtype.ext
    change star (s i)*s j = ((if i=j then (1:S) else 0):S).val
    rw [hs]
    split_ifs <;> rfl
  have he : (S.subtype (cuntzPolynomial t c))=cuntzPolynomial s c := by
    rw [map_cuntzPolynomial]
    rfl
  rw [← he]
  exact norm_cuntzPolynomial_separable t ht c

end NormBound

end

end WeakPureInfiniteness
end

end OAI
