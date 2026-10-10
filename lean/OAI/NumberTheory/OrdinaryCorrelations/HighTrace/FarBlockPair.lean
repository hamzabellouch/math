import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.WalkBetweenSupport
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.FarCorrupted
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.TreeBlocksWithEdges

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.NumericalSubtrees
open OrdinaryCorrelations.ForestTraversal Finset Classical SimpleGraph
noncomputable section
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ K : ℕ}

structure FarBlockPair (w : NumericalLine D h ℓ) (hh : 0<h) (K : ℕ) where
  selected : Finset S.Index
  far : selected ⊆ farCorrupted w K
  first : Block (edgeGraph w.line hh w.line.treeSteps)
  second : Block (edgeGraph w.line hh w.line.treeSteps)
  first_small : first.walk.length ≤ K
  second_small : second.walk.length ≤ K
  witness : ∀ p ∈ selected,CorruptWitness w p
  edge_in : ∀ p hp,treeEdge w.line (witness p hp).edge ∈ first.walk.edges
  vertex_in : ∀ p hp,w.line.offset (witness p hp).vertex ∈ second.walk.support

theorem far_block_pair_exists (w : NumericalLine D h ℓ) (hh : 0<h) (hK : 0<K)
    (hA : (farCorrupted w K).Nonempty) :
    ∃ F : FarBlockPair w hh K,
      (farCorrupted w K).card ≤ ((2*ℓ)/K+1)^2*F.selected.card := by
  obtain ⟨bs,hbs,hsmall,hvertices,hedges⟩ :
      ∃ bs : List (Block (edgeGraph w.line hh w.line.treeSteps)),
      bs.length ≤ (2*ℓ)/K+1 ∧ (∀ b ∈ bs,b.walk.length ≤ K) ∧
      (∀ z ∈ treeVertices w.line,∃ b ∈ bs,z ∈ b.walk.support) ∧
      (∀ e ∈ w.line.treeSteps,∃ b ∈ bs,treeEdge w.line e ∈ b.walk.edges) := by
    exact full_tree_blocks w.line hh K hK
  let A := farCorrupted w K
  let W : ∀ p : A,CorruptWitness w p.val := fun p =>
    Classical.choice (exists_corruptWitness w p.val ((mem_filter.mp (Finset.mem_sdiff.mp p.property).1).2))
  have h1 (p : A) : ∃ i : Fin bs.length,treeEdge w.line (W p).edge ∈ (bs.get i).walk.edges := by
    obtain ⟨b,hb,he⟩ := hedges (W p).edge (W p).tree
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hb
    exact ⟨i,he⟩
  have h2 (p : A) : ∃ i : Fin bs.length,w.line.offset (W p).vertex ∈ (bs.get i).walk.support := by
    have hv : w.line.offset (W p).vertex ∈ treeVertices w.line := mem_image.mpr ⟨_,mem_univ _,rfl⟩
    obtain ⟨b,hb,hv⟩ := hvertices _ hv
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hb
    exact ⟨i,hv⟩
  choose c₁ hc₁ using h1
  choose c₂ hc₂ using h2
  let c (p : A) := (c₁ p,c₂ p)
  let I := (univ : Finset A).image c
  have hI : I.Nonempty := by
    obtain ⟨p,hp⟩ := hA
    exact ⟨c ⟨p,hp⟩,mem_image.mpr ⟨⟨p,hp⟩,mem_univ _,rfl⟩⟩
  obtain ⟨z,hz,hmax⟩ := exists_max_image I (fun k => ((univ : Finset A).filter (fun p => c p=k)).card) hI
  let C := (univ : Finset A).filter (fun p => c p=z)
  have hcount : A.card ≤ bs.length^2*C.card := by
    have he := card_eq_sum_card_image c (univ : Finset A)
    simp only [card_univ,Fintype.card_coe] at he
    calc
      _ = ∑ k ∈ I,((univ : Finset A).filter (fun p => c p=k)).card := he
      _ ≤ ∑ _k ∈ I,C.card := sum_le_sum hmax
      _ = I.card*C.card := by simp
      _ ≤ bs.length^2*C.card := by
        apply Nat.mul_le_mul_right
        have hi := card_le_univ I
        simpa only [Fintype.card_prod,Fintype.card_fin,pow_two] using hi
  let A' := C.image Subtype.val
  have hsub : A' ⊆ A := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := mem_image.mp hp
    exact q.property
  have hcard : A'.card=C.card := card_image_iff.mpr (fun p hp q hq he => Subtype.ext he)
  have hsel (p : S.Index) (hp : p ∈ A') : c ⟨p,hsub hp⟩=z := by
    obtain ⟨q,hq,rfl⟩ := mem_image.mp hp
    exact (mem_filter.mp hq).2
  let F : FarBlockPair w hh K := {
    selected := A'
    far := hsub
    first := bs.get z.1
    second := bs.get z.2
    first_small := hsmall _ (List.get_mem ..)
    second_small := hsmall _ (List.get_mem ..)
    witness p hp := W ⟨p,hsub hp⟩
    edge_in p hp := by
      have he := hc₁ ⟨p,hsub hp⟩
      have hc := congrArg Prod.fst (hsel p hp)
      change c₁ ⟨p,hsub hp⟩=z.1 at hc
      rw [←hc]
      exact he
    vertex_in p hp := by
      have he := hc₂ ⟨p,hsub hp⟩
      have hc := congrArg Prod.snd (hsel p hp)
      change c₂ ⟨p,hsub hp⟩=z.2 at hc
      rw [←hc]
      exact he }
  refine ⟨F,?_⟩
  change A.card ≤ ((2*ℓ)/K+1)^2*A'.card
  rw [hcard]
  exact hcount.trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hbs 2))

namespace FarBlockPair
variable {w : NumericalLine D h ℓ} {hh : 0<h} (F : FarBlockPair w hh K)

lemma endpoints_outside (p : S.Index) (hp : p ∈ F.selected) :
    w.line.offset (F.witness p hp).edge.castSucc ∉ F.second.walk.support ∧
    w.line.offset (F.witness p hp).edge.succ ∉ F.second.walk.support := by
  constructor
  · intro hv
    obtain ⟨q,hq⟩ := walk_between_support F.second.walk hv (F.vertex_in p hp)
    have hl := farCorrupted_walk_long w hh p (F.far hp) (F.witness p hp) (Or.inl rfl) q
    exact (not_lt_of_ge (hq.trans F.second_small)) hl
  · intro hv
    obtain ⟨q,hq⟩ := walk_between_support F.second.walk hv (F.vertex_in p hp)
    have hl := farCorrupted_walk_long w hh p (F.far hp) (F.witness p hp) (Or.inr rfl) q
    exact (not_lt_of_ge (hq.trans F.second_small)) hl

lemma second_path_absent (P : TreePath w K)
    (hP : ∀ j,P.vertex j ∈ F.second.walk.support) :
    ∀ p ∈ F.selected,∀ i,¬(p:ℕ) ∣ w.line.label (P.edge i) := by
  intro p hp i hd
  have hfree : ¬S.IsFixed w.line p := (mem_filter.mp (Finset.mem_sdiff.mp (F.far hp)).1).2.1
  have he : P.edge i=(F.witness p hp).edge :=
    (unique_occurrence_of_free w.line p hfree (F.witness p hp).edge (F.witness p hp).divides (P.edge i)).mp hd
  have hend := P.endpoints i
  cases hf : P.forward i <;> simp only [hf,Bool.false_eq_true,ite_false,ite_true] at hend
  · exact (F.endpoints_outside p hp).2 (he ▸ (hend.1 ▸ hP i.castSucc))
  · exact (F.endpoints_outside p hp).1 (he ▸ (hend.1 ▸ hP i.castSucc))

end FarBlockPair
end
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
