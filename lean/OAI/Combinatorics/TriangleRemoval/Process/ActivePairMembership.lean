import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.GraphCardSqrt
import OAI.Combinatorics.TriangleRemoval.Process.EdgePairNe
import OAI.Combinatorics.TriangleRemoval.Stability.CavityGenerator
import OAI.Combinatorics.TriangleRemoval.Spectral.MatrixInfinityAlgHom
import OAI.Combinatorics.TriangleRemoval.Process.ActiveHypergraph

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

lemma active_pair_membership {n : ℕ} {G : Graph n} (hG : G ⊆ completeGraph n)
    (e f : G) (T : triangles G) :
    e ∈ activeHypergraph G T ∧ f ∈ (activeHypergraph G T).erase e ↔
      e ≠ f ∧ T.val = e.val ∪ f.val := by
  classical
  have he := mem_completeGraph.mp (hG e.property)
  have hf := mem_completeGraph.mp (hG f.property)
  have hT := (mem_triangles.mp T.property).1
  simp only [activeHypergraph_mem,Finset.mem_erase,Finset.mem_powersetCard]
  constructor
  · rintro ⟨⟨het,_⟩,hne,hft,_⟩
    have hne' : e.val ≠ f.val := fun h => hne (Subtype.ext h.symm)
    have h3 := three_le_card_union he hf hne'
    exact ⟨Ne.symm hne,(Finset.eq_of_subset_of_card_le
      (Finset.union_subset het hft) (by omega)).symm⟩
  · rintro ⟨hne,hEq⟩
    exact ⟨⟨hEq ▸ Finset.subset_union_left,he⟩,Ne.symm hne,
      hEq ▸ Finset.subset_union_right,hf⟩

lemma active_pair_sum {n : ℕ} {G : Graph n} (hG : G ⊆ completeGraph n)
    (e f : G) (x : ℝ) :
    (∑ T : triangles G, if e ∈ activeHypergraph G T ∧
      f ∈ (activeHypergraph G T).erase e then x else 0) =
      if e ≠ f ∧ e.val ∪ f.val ∈ triangles G then x else 0 := by
  classical
  simp only [active_pair_membership hG]
  by_cases hh : e ≠ f ∧ e.val ∪ f.val ∈ triangles G
  · rw [ite_eq_left hh]
    let T : triangles G := ⟨e.val ∪ f.val,hh.2⟩
    have hs := Finset.sum_eq_single T (s := Finset.univ)
      (f := fun U : triangles G => if e ≠ f ∧ U.val = e.val ∪ f.val then x else 0)
      (fun U _ hne => ite_eq_right (fun hu => hne (Subtype.ext hu.2)))
      (by simp)
    exact hs.trans (ite_eq_left ⟨hh.1,rfl⟩)
  · rw [ite_eq_right hh]
    apply Finset.sum_eq_zero
    intro T _
    apply ite_eq_right
    rintro ⟨hne,hT⟩
    exact hh ⟨hne,hT ▸ T.property⟩

lemma sum_finset_as_univ {I : Type*} [Fintype I] [DecidableEq I] (S : Finset I) (z : I → ℝ) :
    (∑ i ∈ S, z i) = ∑ i, if i ∈ S then z i else 0 := by
  classical
  rw [← Finset.sum_filter]
  congr 1
  ext i; simp

theorem active_cavityGenerator {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n) (D : ℝ) :
    cavityGenerator (activeHypergraph G) D =
      matrixInfinityAlgHom (D⁻¹ • globalLinkAdjacency G hG) := by
  classical
  apply ContinuousLinearMap.ext
  intro z
  funext e
  rw [cavityGenerator_apply,matrixInfinityAlgHom_apply]
  simp only [Matrix.smul_apply,smul_eq_mul,one_div,mul_assoc,← Finset.mul_sum]
  congr 1
  calc
    _ = ∑ T : triangles G, ∑ f : G, if e ∈ activeHypergraph G T ∧
      f ∈ (activeHypergraph G T).erase e then z f else 0 := by
      simp only [messageCandidates,ne_eq,reduceCtorEq,not_false_eq_true,and_true,
        Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro T _
      rw [sum_finset_as_univ]
      by_cases he : e ∈ activeHypergraph G T
      · simp only [he,ite_true,true_and]
      · simp only [he,ite_false,false_and,Finset.sum_const_zero]
    _ = ∑ f : G, globalLinkAdjacency G hG e f * z f := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro f _
      rw [active_pair_sum hG,globalLinkAdjacency_entry]
      split_ifs <;> simp

lemma active_messageCandidates_card {n : ℕ} (G : Graph n) (e : G) :
    (messageCandidates (activeHypergraph G) e none).card = triangleDegree G e.val := by
  classical
  have hm : (messageCandidates (activeHypergraph G) e none).map (triangleEmbedding G) =
      incidentTriangles G e.val := by
    ext T
    simp only [Finset.mem_map,messageCandidates,Finset.mem_filter,Finset.mem_univ,
      true_and,activeHypergraph_mem,ne_eq,reduceCtorEq,not_false_eq_true,and_true,
      triangleEmbedding,Function.Embedding.coeFn_mk,incidentTriangles]
    constructor
    · rintro ⟨U,hu,rfl⟩
      exact ⟨U.property,hu⟩
    · rintro ⟨hT,he⟩
      exact ⟨⟨T,hT⟩,he,rfl⟩
  have hh := congrArg Finset.card hm
  simpa only [Finset.card_map,triangleDegree] using hh

theorem goodPrefix_cavity_semigroup {c : ℝ} (hc : 0 < c) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∃ J : ℕ, ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (C : ℝ) (G : Graph n) (_h : GoodPrefixGraph n c C G),
      ∀ s ∈ Set.Icc (0 : ℝ) (Real.log n),
        ‖NormedSpace.exp ((-s) • cavityGenerator (activeHypergraph G) (prefixD n))‖ ≤
          C₁*(1+Real.log n)^J := by
  obtain ⟨C₁,hC,J,hb⟩ := goodPrefix_uniform_semigroup hc
  refine ⟨C₁,hC,J,hb.mono ?_⟩
  intro n hn C G h s hs
  rw [active_cavityGenerator G h.1,matrixInfinityAlgHom_exp_norm]
  exact hn C G h s hs
end SharpTerminalLeave

end

end OAI
