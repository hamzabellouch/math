import Mathlib
import OAI.Combinatorics.KMedian.Reduction.LocalCompletion

namespace OAI

section
section
namespace MetricKMedian.Reduction
open Finset

variable {I : Instance}
local instance : PseudoMetricSpace (Fin I.n) := I.pseudoMetric

namespace CloseCenters
variable {G O : Finset (Fin I.n)} {δ : ℝ}

theorem complete_of_choices (C : CloseCenters I G O δ) (hδ : 0 ≤ δ) (hsmall : δ ≤ 1/6)
    (hO : O.Nonempty) (F : Finset (Fin I.n)) (hOF : O ⊆ F)
    (a : ↥G → Fin I.n) (ha : ∀ t, a t ∈ F) (hclose : ∀ t, dist t.val (a t) ≤ δ*C.radius t)
    (hloc : ∀ t, (∑ j ∈ C.region t, nearest I j (insert (a t) C.backup)) ≤
      ∑ j ∈ C.region t, nearest I j (insert (C.matchTo t) C.backup)) :
    let S := C.backup ∪ univ.image a
    S ⊆ F ∧ S.Nonempty ∧ S.card ≤ O.card ∧ cost I S ≤ (1+12*δ)*cost I O := by
  classical
  dsimp only
  let S := C.backup ∪ univ.image a
  have hbS : C.backup ⊆ S := subset_union_left
  have haS : ∀ t, a t ∈ S := fun t => mem_union_right _ (mem_image_of_mem a (mem_univ t))
  have hinsert : ∀ t, insert (a t) C.backup ⊆ S := fun t => insert_subset (haS t) hbS
  have hSF : S ⊆ F := by
    intro i hi
    obtain hb | hm := mem_union.mp hi
    · exact hOF (mem_sdiff.mp hb).1
    · obtain ⟨t,_,rfl⟩ := mem_image.mp hm
      exact ha t
  have hS : S.Nonempty := by
    obtain ⟨i,hi⟩ := hO
    obtain hb | ⟨t,_⟩ := C.optimal_mem hi
    · exact ⟨i,hbS hb⟩
    · exact ⟨a t,haS t⟩
  have hmcard : C.matched.card=G.card := by
    rw [matched,card_image_of_injective _ (C.match_injective hδ (by linarith)),card_univ,
      Fintype.card_coe]
  have hbudget : S.card ≤ O.card := by
    have he : C.backup.card+G.card=O.card := by
      rw [← hmcard]
      exact card_sdiff_add_card_eq_card C.matched_sub
    calc
      S.card ≤ C.backup.card+(univ.image a).card := card_union_le _ _
      _ ≤ C.backup.card+G.card := by
        apply Nat.add_le_add_left
        simpa only [card_univ,Fintype.card_coe] using card_image_le (f:=a) (s:=univ)
      _ = O.card := he
  refine ⟨hSF,hS,hbudget,?_⟩
  have hlocal : ∀ t, (∑ j ∈ C.region t, nearest I j S) ≤
      ∑ j ∈ C.region t, nearest I j O := by
    intro t
    calc
      _ ≤ ∑ j ∈ C.region t, nearest I j (insert (a t) C.backup) :=
        sum_le_sum (fun j _ => I.nearest_antitone j (insert_nonempty _ _) (hinsert t))
      _ ≤ ∑ j ∈ C.region t, nearest I j (insert (C.matchTo t) C.backup) := hloc t
      _ ≤ _ := sum_le_sum (fun j hj => C.region_reference hδ hsmall hO t hj)
  let L := univ.biUnion C.region
  have hLsub : L ⊆ I.clients := by
    intro j hj
    obtain ⟨t,_,ht⟩ := mem_biUnion.mp hj
    exact (mem_filter.mp ht).1
  have hdisj : Set.PairwiseDisjoint (↑(univ : Finset ↥G)) C.region := by
    intro t _ u _ htu
    exact C.region_disjoint htu
  have hnear : (∑ j ∈ L, nearest I j S) ≤ ∑ j ∈ L, nearest I j O := by
    simp only [L,sum_biUnion hdisj]
    exact sum_le_sum (fun t _ => hlocal t)
  have hfar : ∀ j ∈ I.clients \ L, nearest I j S ≤ (1+12*δ)*nearest I j O := by
    intro j hj
    obtain ⟨hjJ,hjL⟩ := mem_sdiff.mp hj
    obtain ⟨i,hi,he⟩ := I.nearest_attained j O hO
    obtain hb | ⟨t,rfl⟩ := C.optimal_mem hi
    · calc
        nearest I j S ≤ nearest I j O := by rw [he]; exact I.nearest_le j (hbS hb)
        _ ≤ (1+12*δ)*nearest I j O := by
          nlinarith only [I.nearest_nonneg j O,mul_nonneg hδ (I.nearest_nonneg j O)]
    · have hout : C.radius t/3 ≤ dist j t.val := by
        have hn : ¬dist j t.val ≤ C.radius t/3 := by
          intro hn
          exact hjL (mem_biUnion.mpr ⟨t,mem_univ _,mem_filter.mpr ⟨hjJ,hn⟩⟩)
        exact (lt_of_not_ge hn).le
      rw [he]
      exact (I.nearest_le j (haS t)).trans (C.outside_connection hδ hsmall t hout (hclose t))
  have hfarSum : (∑ j ∈ I.clients \ L, nearest I j S) ≤
      (1+12*δ)*∑ j ∈ I.clients \ L, nearest I j O := by
    rw [mul_sum]
    exact sum_le_sum hfar
  have hnearSum : (∑ j ∈ L, nearest I j S) ≤ (1+12*δ)*∑ j ∈ L, nearest I j O := by
    apply hnear.trans
    have hnp : 0 ≤ ∑ j ∈ L, nearest I j O := sum_nonneg (fun j _ => I.nearest_nonneg j O)
    have hp := mul_nonneg hδ hnp
    nlinarith only [hp]
  change (∑ j ∈ I.clients, nearest I j S) ≤ (1+12*δ)*∑ j ∈ I.clients, nearest I j O
  calc
    _ = (∑ j ∈ I.clients \ L, nearest I j S)+(∑ j ∈ L, nearest I j S) := (sum_sdiff hLsub).symm
    _ ≤ (1+12*δ)*(∑ j ∈ I.clients \ L, nearest I j O)+
        (1+12*δ)*(∑ j ∈ L, nearest I j O) := add_le_add hfarSum hnearSum
    _ = _ := by rw [← mul_add,sum_sdiff hLsub]

theorem complete (C : CloseCenters I G O δ) (hδ : 0 ≤ δ) (hsmall : δ ≤ 1/6)
    (hO : O.Nonempty) (F : Finset (Fin I.n)) (hOF : O ⊆ F) :
    ∃ a : ↥G → Fin I.n,
      (∀ t, a t ∈ F ∧ dist t.val (a t) ≤ δ*C.radius t) ∧
      let S := C.backup ∪ univ.image a
      S ⊆ F ∧ S.Nonempty ∧ S.card ≤ O.card ∧
      cost I S ≤ (1+12*δ)*cost I O := by
  classical
  choose a ha hclose hloc using C.choose_local F hOF
  exact ⟨a,(fun t => ⟨ha t,hclose t⟩),C.complete_of_choices hδ hsmall hO F hOF a ha hclose hloc⟩

end CloseCenters
end MetricKMedian.Reduction
end
end

end OAI
