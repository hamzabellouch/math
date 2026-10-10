import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.ModifiedWeightSameBand

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.NumericalSubtrees
open Finset Classical
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ L : ℕ}

def activeComponents (w : ClosedLine h ℓ) (hh : 0 < h) (p : S.Index)
    (a : ZMod (p : ℕ)) : Finset (edgeGraph w hh (litEdges w p a)).ConnectedComponent :=
  ((treeVertices w).filter (fun (v : ℤ) => a + (v : ZMod (p : ℕ)) = 0)).image
    (edgeGraph w hh (litEdges w p a)).connectedComponentMk

lemma lit_components_subset_active (w : ClosedLine h ℓ) (hh : 0 < h) (p : S.Index)
    (a : ZMod (p : ℕ)) :
    edgeComponents w hh (litEdges w p a) ⊆ activeComponents w hh p a := by
  intro c hc
  obtain ⟨e,he,rfl⟩ := mem_image.mp hc
  exact mem_image.mpr ⟨w.offset e.castSucc,
    mem_filter.mpr ⟨departure_mem_vertices w e,(mem_filter.mp he).2⟩,rfl⟩

lemma activeConnected_iff_card (w : ClosedLine h ℓ) (hh : 0 < h) (p : S.Index)
    (a : ZMod (p : ℕ)) :
    ActiveConnected w hh p a ↔ (activeComponents w hh p a).card ≤ 1 := by
  rw [card_le_one]
  constructor
  · intro hc c hc' d hd'
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hc'
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hd'
    exact SimpleGraph.ConnectedComponent.sound
      (hc u (mem_filter.mp hu).1 v (mem_filter.mp hv).1 (mem_filter.mp hu).2 (mem_filter.mp hv).2)
  · intro hc u hu v hv hau hav
    exact SimpleGraph.ConnectedComponent.exact (hc _
      (mem_image.mpr ⟨u,mem_filter.mpr ⟨hu,hau⟩,rfl⟩) _
      (mem_image.mpr ⟨v,mem_filter.mpr ⟨hv,hav⟩,rfl⟩))

lemma lit_components_le_one (w : ClosedLine h ℓ) (hh : 0 < h) (p : S.Index)
    (a : ZMod (p : ℕ)) (hc : ActiveConnected w hh p a) :
    (edgeComponents w hh (litEdges w p a)).card ≤ 1 :=
  (card_le_card (lit_components_subset_active w hh p a)).trans
    ((activeConnected_iff_card w hh p a).mp hc)

def unlitOccurrences (w : ClosedLine h ℓ) (p : S.Index) (a : ZMod (p : ℕ)) : Finset (Fin ℓ) :=
  univ.filter (fun i => (p : ℕ) ∣ w.label i ∧ a + (w.offset i.castSucc : ZMod (p : ℕ)) ≠ 0)

lemma ghosts_le_unlit (w : ClosedLine h ℓ) (p : S.Index) (a : ZMod (p : ℕ)) :
    ((treeOccurrences w p) \ litEdges w p a).card ≤ (unlitOccurrences w p a).card := by
  apply card_le_card
  intro e he
  have ho := (mem_sdiff.mp he).1
  have hnl : a + (w.offset e.castSucc : ZMod (p : ℕ)) ≠ 0 := by
    intro ha
    exact (mem_sdiff.mp he).2 (mem_filter.mpr ⟨ho,ha⟩)
  exact mem_filter.mpr ⟨mem_univ e,(mem_filter.mp ho).2,hnl⟩

lemma taggedPieces_card_le (w : ClosedLine h ℓ) (hh : 0 < h) (O E : Finset (Fin ℓ)) :
    (taggedPieces w hh O E).card ≤ (edgeComponents w hh E).card+(O\E).card := by
  exact (card_union_le _ _).trans (Nat.add_le_add card_image_le card_image_le)

lemma tagged_fixed_card (w : ClosedLine h ℓ) (hh : 0 < h)
    (𝔏 : List (AttachedSpec w D L)) (a : S.FixedResidues w) (p : S.FixedIndex w) (K : ℕ)
    (hK : (treeOccurrences w p.val).Nonempty → (activeComponents w hh p.val (a p)).card ≤ K) :
    (taggedTokens w hh 𝔏 (recordAt w hh 𝔏 a) p.val).card ≤
      (if ¬ ActiveConnected w hh p.val (a p) then K else 0) +
      2*(unlitOccurrences w p.val (a p)).card +
      (if (p.val : ℕ) ∈ listSupport w 𝔏 then 1 else 0) := by
  by_cases ho : (treeOccurrences w p.val).Nonempty
  · by_cases ht : (recordAt w hh 𝔏 a).2 p.val = true
    · have hc : (taggedTokens w hh 𝔏 (recordAt w hh 𝔏 a) p.val).card ≤
          (edgeComponents w hh (litEdges w p.val (a p))).card +
          (unlitOccurrences w p.val (a p)).card := by
        apply (card_filter_le ..).trans
        rw [recordTokens,ite_eq_left ho,ite_eq_left p.property,ite_eq_left ht,recordAt_edges]
        exact (taggedPieces_card_le w hh _ _).trans
          (Nat.add_le_add_left (ghosts_le_unlit w p.val (a p)) _)
      by_cases hconn : ActiveConnected w hh p.val (a p)
      · rw [ite_eq_right (not_not.mpr hconn)]
        have hcone := lit_components_le_one w hh p.val (a p) hconn
        have htag := (recordAt_tag w hh 𝔏 a p ho).mp ht
        rcases htag with hlist | hn | hu
        · rw [ite_eq_left hlist]; omega
        · exact (hn hconn).elim
        · have hupos : 0 < (unlitOccurrences w p.val (a p)).card := by
            obtain ⟨i,hi,ha⟩ := hu
            exact card_pos.mpr ⟨i,mem_filter.mpr ⟨mem_univ i,hi,ha⟩⟩
          split_ifs <;> omega
      · rw [ite_eq_left hconn]
        have hcomp := (card_le_card (lit_components_subset_active w hh p.val (a p))).trans (hK ho)
        omega
    · simp only [taggedTokens,recordTokens,ho,ite_true,p.property,ht,Bool.false_eq_true,ite_false]
      rw [filter_singleton,ite_eq_right (by simp),card_empty]
      exact Nat.zero_le _
  · simp only [taggedTokens,recordTokens,ho,ite_false,filter_empty,card_empty]
    omega

lemma free_tree_card_le_one (w : ClosedLine h ℓ) (p : S.Index) (hp : ¬S.IsFixed w p) :
    (treeOccurrences w p).card ≤ 1 := by
  apply card_le_one.mpr
  intro e he j hj
  exact (unique_occurrence_of_free w p hp j (mem_filter.mp hj).2 e).mp (mem_filter.mp he).2

def freeCorrupted (w : ClosedLine h ℓ) (p : S.Index) : Prop :=
  ¬ S.IsFixed w p ∧ ∃ e ∈ treeOccurrences w p, ¬ w.Uncorrupted (p : ℕ) e

lemma tagged_free_card (w : ClosedLine h ℓ) (hh : 0 < h)
    (𝔏 : List (AttachedSpec w D L)) (a : S.FixedResidues w) (p : S.Index)
    (hp : ¬ S.IsFixed w p) :
    (taggedTokens w hh 𝔏 (recordAt w hh 𝔏 a) p).card ≤
      (if freeCorrupted w p then 1 else 0) +
      (if (p : ℕ) ∈ listSupport w 𝔏 then 1 else 0) := by
  by_cases ho : (treeOccurrences w p).Nonempty
  · have hc : (taggedTokens w hh 𝔏 (recordAt w hh 𝔏 a) p).card ≤ 1 := by
      apply (card_filter_le ..).trans
      rw [recordTokens,ite_eq_left ho,ite_eq_right hp]
      exact card_image_le.trans (free_tree_card_le_one w p hp)
    by_cases hcor : freeCorrupted w p
    · rw [ite_eq_left hcor]; omega
    · by_cases hlist : (p : ℕ) ∈ listSupport w 𝔏
      · rw [ite_eq_left hlist]; omega
      · have hz : taggedTokens w hh 𝔏 (recordAt w hh 𝔏 a) p = ∅ := by
          apply eq_empty_iff_forall_notMem.mpr
          intro t ht
          have hh' := mem_filter.mp ht
          rw [recordTokens,ite_eq_left ho,ite_eq_right hp] at hh'
          obtain ⟨e,he,rfl⟩ := mem_image.mp hh'.1
          have hnt : ¬singletonIsTagged w 𝔏 p e := by
            intro ht
            rcases ht with hl | hbad
            · exact hlist hl
            · exact hcor ⟨hp,e,he,hbad⟩
          simp only [freePiece,ite_eq_right hnt] at hh'
          cases hh'.2
        rw [hz,card_empty]; omega
  · simp only [taggedTokens,recordTokens,ho,ite_false,filter_empty,card_empty]
    omega

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
