import Mathlib
import OAI.Analysis.WeakInfiniteness.OInfinityCriterion
import OAI.Analysis.WeakInfiniteness.UnitaryIntertwining

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

universe u v

section Polynomial

variable {A : Type u} {D : Type v} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra D]

def minimalPolynomial (c : A × D →₀ ℂ) : MinimalTensor A D :=
  c.sum fun p t => t • minimalElementary p.1 p.2

lemma minimalPolynomial_denseRange : DenseRange (minimalPolynomial (A := A) (D := D)) := by
  let S := Submodule.span ℂ (Set.range fun p : A × D => minimalElementary p.1 p.2)
  have h : S.topologicalClosure=⊤ := by
    apply minimal_elementary_span_dense _ S.isClosed_topologicalClosure
    intro a d
    exact S.le_topologicalClosure (Submodule.subset_span (Set.mem_range_self (a,d)))
  have hr : Set.range (minimalPolynomial (A := A) (D := D))=(S : Set (MinimalTensor A D)) := by
    ext x
    exact Finsupp.mem_span_range_iff_exists_finsupp.symm
  intro z
  rw [hr]
  change z ∈ S.topologicalClosure
  rw [h]
  trivial

end Polynomial

section UnitalRight

variable {A : Type u} {D : Type v} [NonUnitalCStarAlgebra A] [CStarAlgebra D]

def ElementaryUnitaryIntertwining (A : Type u) (D : Type v)
    [NonUnitalCStarAlgebra A] [CStarAlgebra D] : Prop :=
  ∀ (E : Finset A) (T : Finset (A × D)) (ε : ℝ), 0 < ε →
    ∃ u : unitary (Unitization ℂ (MinimalTensor A D)),
      (∀ a ∈ E,dist (unitizationInnerFun u (minimalLeftEmbedding A D a))
        (minimalLeftEmbedding A D a)<ε) ∧
      ∀ p ∈ T,∃ a : A,dist (unitizationInnerFun u (minimalLeftEmbedding A D a))
        (minimalElementary p.1 p.2)<ε

lemma ElementaryUnitaryIntertwining.unitaryFiniteIntertwining
    (h : ElementaryUnitaryIntertwining A D) :
    UnitaryFiniteIntertwining (minimalLeftEmbedding A D) := by
  classical
  intro E F ε hε
  have hd : ∀ z : MinimalTensor A D,∃ c : A × D →₀ ℂ,
      dist (minimalPolynomial c) z<ε/2 := by
    intro z
    simpa only [dist_comm] using
      Metric.denseRange_iff.mp minimalPolynomial_denseRange z (ε/2) (by positivity)
  choose c hc using hd
  let T : Finset (A × D) := F.biUnion fun z =>
    (c z).support.image (fun p => ((c z p) • p.1,p.2))
  let N : ℝ := 1+∑ z ∈ F,((c z).support.card : ℝ)
  have hN : 0 < N := by dsimp only [N]; positivity
  have hN1 : 1 ≤ N := by
    dsimp only [N]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)
  let δ : ℝ := ε/(4*N)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hδε : δ < ε := by
    dsimp only [δ]
    apply (div_lt_iff₀ (by positivity : 0 < 4*N)).mpr
    nlinarith
  obtain ⟨u,hE,hT⟩ := h E T δ hδ
  have hw : ∀ p : A × D,∃ a : A,p ∈ T →
      dist (unitizationInnerFun u (minimalLeftEmbedding A D a)) (minimalElementary p.1 p.2)<δ := by
    intro p
    by_cases hp : p ∈ T
    · obtain ⟨a,ha⟩ := hT p hp
      exact ⟨a,fun _ => ha⟩
    · exact ⟨0,fun h => (hp h).elim⟩
  choose w hw using hw
  refine ⟨u,fun a ha => (hE a ha).trans hδε,?_⟩
  intro z hz
  let g : A × D → A × D := fun p => ((c z p) • p.1,p.2)
  let a : A := ∑ p ∈ (c z).support,w (g p)
  have hg (p : A × D) (hp : p ∈ (c z).support) : g p ∈ T := by
    exact Finset.mem_biUnion.mpr ⟨z,hz,Finset.mem_image.mpr ⟨p,hp,rfl⟩⟩
  have hn : ((c z).support.card : ℝ) ≤ N := by
    have hs := Finset.single_le_sum (f := fun y : MinimalTensor A D => ((c y).support.card : ℝ))
      (fun _ _ => Nat.cast_nonneg _) hz
    dsimp only [N]
    linarith
  have he : dist (unitizationInnerFun u (minimalLeftEmbedding A D a)) (minimalPolynomial (c z))
      ≤ ((c z).support.card : ℝ)*δ := by
    rw [dist_eq_norm]
    change ‖unitizationInnerHom u (minimalLeftEmbedding A D a)-minimalPolynomial (c z)‖ ≤ _
    dsimp only [a,minimalPolynomial,Finsupp.sum]
    rw [map_sum,map_sum,← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ p ∈ (c z).support,
          ‖unitizationInnerHom u (minimalLeftEmbedding A D (w (g p)))-
            c z p • minimalElementary p.1 p.2‖ := norm_sum_le _ _
      _ ≤ ∑ _p ∈ (c z).support,δ := by
        apply Finset.sum_le_sum
        intro p hp
        have hp' := (hw (g p) (hg p hp)).le
        rw [dist_eq_norm] at hp'
        change ‖unitizationInnerHom u (minimalLeftEmbedding A D (w (g p)))-
          minimalElementary (c z p • p.1) p.2‖ ≤ δ at hp'
        rwa [minimalElementary_smul_left] at hp'
      _ = _ := by simp
  refine ⟨a,?_⟩
  have hdist := dist_triangle (unitizationInnerFun u (minimalLeftEmbedding A D a))
    (minimalPolynomial (c z)) z
  have hNδ : N*δ=ε/4 := by dsimp only [δ]; field_simp
  have hbound := mul_le_mul_of_nonneg_right hn hδ.le
  rw [hNδ] at hbound
  have hcz := hc z
  linarith

lemma ElementaryUnitaryIntertwining.finiteIntertwining
    (h : ElementaryUnitaryIntertwining A D) :
    FiniteIntertwining (minimalLeftEmbedding A D) :=
  h.unitaryFiniteIntertwining.finiteIntertwining

end UnitalRight

def oInfinityAbsorptionEquiv_of_elementaryIntertwining (A : Type u)
    [NonUnitalCStarAlgebra A] [SeparableSpace A]
    (h : ElementaryUnitaryIntertwining A OInfinity) :
    A ≃⋆ₐ[ℂ] MinimalTensor A OInfinity :=
  oInfinityAbsorptionEquiv_of_finiteIntertwining A h.finiteIntertwining

end

end WeakPureInfiniteness
end

end OAI
