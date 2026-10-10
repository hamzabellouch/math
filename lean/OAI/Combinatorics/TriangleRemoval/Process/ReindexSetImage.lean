import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.ReindexSet

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

@[simp] lemma reindexSet_image {N : ℕ} (s : Finset (Fin N)) (J : Finset (Fin s.card)) :
    reindexSet s (J.image (s.orderEmbOfFin rfl)) = J := by
  ext i
  simp only [mem_reindexSet,Finset.mem_image]
  constructor
  · rintro ⟨j,hj,he⟩
    exact (s.orderEmbOfFin rfl).injective he ▸ hj
  · intro hi
    exact ⟨i,hi,rfl⟩

lemma reindexTemplate_free_card {N : ℕ} (Z I : Finset (Fin N)) (E : Graph N)
    (hE : ∀ e ∈ E, e ⊆ Z ∪ I) (hsimple : ∀ e ∈ E, e.card = 2)
    (hind : ∀ e ∈ E, ¬ e ⊆ I) (hd : Disjoint Z I) :
    (Z ∪ I).card - (reindexTemplate (Z ∪ I) E I hE hsimple hind).roots.card = Z.card := by
  rw [reindexTemplate_roots_card _ _ _ _ _ _ Finset.subset_union_right,
    Finset.card_union_of_disjoint hd]
  omega

theorem reindexTemplate_sparse_transfer {N : ℕ} (Z I : Finset (Fin N)) (E : Graph N)
    (hE : ∀ e ∈ E, e ⊆ Z ∪ I) (hsimple : ∀ e ∈ E, e.card = 2)
    (hind : ∀ e ∈ E, ¬ e ⊆ I) (hd : Disjoint Z I)
    (hsparse : ∀ U ⊆ Z, U ≠ Z → (E.filter (fun e => e ⊆ I ∪ U)).card ≤ 2 * U.card) :
    let T := reindexTemplate (Z ∪ I) E I hE hsimple hind
    ∀ J : Finset (Fin (Z ∪ I).card), T.roots ⊆ J → J ≠ Finset.univ →
      (T.edges.filter (· ⊆ J)).card ≤ 2 * (J.card - T.roots.card) := by
  intro T J hJ hproper
  let s := Z ∪ I
  let f := s.orderEmbOfFin rfl
  let Js := J.image f
  let U := Js ∩ Z
  have hJs : Js ⊆ s := by
    intro x hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    exact s.orderEmbOfFin_mem rfl i
  have hI : I ⊆ Js := by
    intro x hx
    rw [← image_reindexSet (s := s) (e := I) Finset.subset_union_right] at hx
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr ⟨i,hJ hi,rfl⟩
  have hU : U ⊆ Z := Finset.inter_subset_right
  have hUnion : I ∪ U = Js := by
    apply Finset.Subset.antisymm
    · exact Finset.union_subset hI Finset.inter_subset_left
    · intro x hx
      rcases Finset.mem_union.mp (hJs hx) with hxZ | hxI
      · exact Finset.mem_union_right I (Finset.mem_inter.mpr ⟨hx,hxZ⟩)
      · exact Finset.mem_union_left U hxI
  have hUne : U ≠ Z := by
    intro he
    have hJall : Js = s := by rw [← hUnion,he]; exact Finset.union_comm _ _
    apply hproper
    apply Finset.eq_univ_of_forall
    intro i
    have hm : f i ∈ Js := by
      rw [hJall]
      exact s.orderEmbOfFin_mem rfl i
    obtain ⟨j,hj,he⟩ := Finset.mem_image.mp hm
    exact f.injective he ▸ hj
  have hcardJs : Js.card = J.card := Finset.card_image_of_injective _ f.injective
  have hdis : Disjoint I U := hd.symm.mono_right hU
  have hcard : J.card - T.roots.card = U.card := by
    have hh := Finset.card_union_of_disjoint hdis
    rw [hUnion,hcardJs] at hh
    have hroot : T.roots.card = I.card := reindexTemplate_roots_card _ _ _ _ _ _
      Finset.subset_union_right
    rw [hroot]
    omega
  have hinduced : (T.edges.filter (· ⊆ J)).card = (E.filter (· ⊆ I ∪ U)).card := by
    have hh := reindexTemplate_induced_card s E I hE hsimple hind Js
    rw [reindexSet_image] at hh
    rw [hUnion]
    exact hh
  rw [hinduced,hcard]
  exact hsparse U hU hUne

end SharpTerminalLeave

end

end OAI
