import Mathlib
import OAI.Analysis.WeakInfiniteness.ElementaryIntertwining
import OAI.Analysis.WeakInfiniteness.TensorNorm

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

universe u v

variable (A : Type u) (D : Type v) [CStarAlgebra A] [CStarAlgebra D]

def ApproximatelyCentralCopies : Prop :=
  ∀ (E : Finset A) (K : Finset D) (ε : ℝ),0<ε →
    ∃ θ : D →⋆ₐ[ℂ] A,∀ a ∈ E,∀ d ∈ K,‖θ d*a-a*θ d‖<ε

variable {A D}

def tensorCopyMap (θ : D →⋆ₐ[ℂ] A) : MinimalTensor D D →⋆ₙₐ[ℂ] MinimalTensor A D :=
  minimalMapAny θ.toNonUnitalStarAlgHom (NonUnitalStarAlgHom.id ℂ D)

@[simp] lemma tensorCopyMap_elementary (θ : D →⋆ₐ[ℂ] A) (d e : D) :
    tensorCopyMap θ (minimalElementary d e)=minimalElementary (θ d) e := by
  simp only [tensorCopyMap,minimalMapAny_elementary,StarAlgHom.coe_toNonUnitalStarAlgHom,
    NonUnitalStarAlgHom.coe_id, id_eq]

lemma tensorCopyMap_polynomial_commutator (θ : D →⋆ₐ[ℂ] A) (c : D × D →₀ ℂ) (a : A) :
    tensorCopyMap θ (minimalPolynomial c)*minimalLeftEmbedding A D a-
      minimalLeftEmbedding A D a*tensorCopyMap θ (minimalPolynomial c)=
      c.sum (fun p t => t • minimalElementary (θ p.1*a-a*θ p.1) p.2) := by
  simp only [minimalPolynomial,Finsupp.sum,map_sum,map_smul,
    Finset.sum_mul,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  change c p • tensorCopyMap θ (minimalElementary p.1 p.2)*minimalElementary a 1-
    minimalElementary a 1*(c p • tensorCopyMap θ (minimalElementary p.1 p.2))=_
  rw [tensorCopyMap_elementary,smul_mul_assoc,mul_smul_comm,← smul_sub]
  congr 1
  rw [← minimalElementary_mul,← minimalElementary_mul,mul_one,one_mul]
  exact (map_sub (minimalElementaryLeftLinear p.2) (θ p.1*a) (a*θ p.1)).symm

lemma norm_tensorCopyMap_polynomial_commutator_le (θ : D →⋆ₐ[ℂ] A)
    (c : D × D →₀ ℂ) (a : A) (η : ℝ)
    (hc : ∀ p ∈ c.support,‖θ p.1*a-a*θ p.1‖≤η) :
    ‖tensorCopyMap θ (minimalPolynomial c)*minimalLeftEmbedding A D a-
      minimalLeftEmbedding A D a*tensorCopyMap θ (minimalPolynomial c)‖ ≤
      (∑ p ∈ c.support,‖c p‖*‖p.2‖)*η := by
  rw [tensorCopyMap_polynomial_commutator]
  dsimp only [Finsupp.sum]
  calc
    _ ≤ ∑ p ∈ c.support,‖c p • minimalElementary (θ p.1*a-a*θ p.1) p.2‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ c.support,(‖c p‖*‖p.2‖)*η := by
      apply Finset.sum_le_sum
      intro p hp
      rw [norm_smul,norm_minimalElementary]
      have hh := mul_le_mul_of_nonneg_left (hc p hp) (mul_nonneg (norm_nonneg (c p)) (norm_nonneg p.2))
      nlinarith
    _ = _ := (Finset.sum_mul _ _ _).symm

lemma norm_commutator_perturb_le (x y b : MinimalTensor A D) :
    ‖x*b-b*x‖ ≤ 2*‖b‖*‖x-y‖+‖y*b-b*y‖ := by
  have he : x*b-b*x=(x-y)*b-b*(x-y)+(y*b-b*y) := by noncomm_ring
  rw [he]
  calc
    _ ≤ ‖(x-y)*b-b*(x-y)‖+‖y*b-b*y‖ := norm_add_le _ _
    _ ≤ (‖(x-y)*b‖+‖b*(x-y)‖)+‖y*b-b*y‖ := add_le_add (norm_sub_le _ _) (le_refl _)
    _ ≤ (‖x-y‖*‖b‖+‖b‖*‖x-y‖)+‖y*b-b*y‖ := by
      gcongr <;> exact norm_mul_le _ _
    _ = _ := by ring

lemma ApproximatelyCentralCopies.tensor_commutator (h : ApproximatelyCentralCopies A D)
    (E : Finset A) (z : MinimalTensor D D) (ε : ℝ) (hε : 0<ε) :
    ∃ θ : D →⋆ₐ[ℂ] A,∀ a ∈ E,
      ‖tensorCopyMap θ z*minimalLeftEmbedding A D a-
        minimalLeftEmbedding A D a*tensorCopyMap θ z‖<ε := by
  classical
  let M : ℝ := 1+∑ a ∈ E,‖a‖
  have hM : 0<M := by dsimp only [M]; positivity
  have haM (a : A) (ha : a ∈ E) : ‖a‖≤M := by
    have hh := Finset.single_le_sum (f := fun b : A => ‖b‖) (fun _ _ => norm_nonneg _) ha
    dsimp only [M]; linarith
  obtain ⟨c,hc⟩ := Metric.denseRange_iff.mp
    (minimalPolynomial_denseRange (A := D) (D := D)) z (ε/(8*M)) (by positivity)
  have hcz : ‖z-minimalPolynomial c‖<ε/(8*M) := by simpa only [dist_eq_norm] using hc
  let C : ℝ := 1+∑ p ∈ c.support,‖c p‖*‖p.2‖
  have hC : 0<C := by dsimp only [C]; positivity
  let η := ε/(4*C)
  have hη : 0<η := by dsimp only [η]; positivity
  obtain ⟨θ,hθ⟩ := h E (c.support.image Prod.fst) η hη
  refine ⟨θ,?_⟩
  intro a ha
  have hpoly := norm_tensorCopyMap_polynomial_commutator_le θ c a η (fun p hp =>
    (hθ a ha p.1 (Finset.mem_image.mpr ⟨p,hp,rfl⟩)).le)
  have href := norm_commutator_perturb_le (tensorCopyMap θ z)
    (tensorCopyMap θ (minimalPolynomial c)) (minimalLeftEmbedding A D a)
  have hnorm : ‖tensorCopyMap θ z-tensorCopyMap θ (minimalPolynomial c)‖≤‖z-minimalPolynomial c‖ := by
    rw [← map_sub]
    exact NonUnitalStarAlgHom.norm_apply_le _ _
  have hleft : ‖minimalLeftEmbedding A D a‖≤M :=
    (NonUnitalStarAlgHom.norm_apply_le _ _).trans (haM a ha)
  have herror : 2*‖minimalLeftEmbedding A D a‖*
      ‖tensorCopyMap θ z-tensorCopyMap θ (minimalPolynomial c)‖≤ε/4 := by
    calc
      _ ≤ 2*M*(ε/(8*M)) := by gcongr; exact hnorm.trans hcz.le
      _ = _ := by field_simp; ring
  have hsum : (∑ p ∈ c.support,‖c p‖*‖p.2‖)*η ≤ ε/4 := by
    calc
      _ ≤ C*η := mul_le_mul_of_nonneg_right (by dsimp only [C]; linarith) hη.le
      _ = _ := by dsimp only [η]; field_simp
  linarith

end

end WeakPureInfiniteness
end

end OAI
