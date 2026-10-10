import Mathlib
import OAI.Combinatorics.TriangleRemoval.Coupling.OrderEmbRank

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

def orderedSuffix {N : ℕ} (S : Finset (Fin N)) (R : ℕ) : Finset (Fin N) :=
  S.filter (fun x => R ≤ x.val)

lemma prefix_suffix_card {N R : ℕ} (S : Finset (Fin N)) (hR : R ≤ N)
    (hroot : ∀ x : Fin N, x.val < R → x ∈ S) :
    S.card = R + (orderedSuffix S R).card := by
  have he : S.filter (fun x => x.val < R) = Finset.univ.filter (fun x => x.val < R) := by
    ext x
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨And.right,fun hx => ⟨hroot x hx,hx⟩⟩
  have hh := Finset.card_filter_add_card_filter_not (s := S) (fun x => x.val < R)
  rw [he,Fin.card_filter_val_lt,Nat.min_eq_right hR] at hh
  simpa only [orderedSuffix,Nat.not_lt] using hh.symm

lemma suffix_full_rank {N R : ℕ} (S : Finset (Fin N)) (hR : R ≤ N)
    (hroot : ∀ x : Fin N, x.val < R → x ∈ S)
    (i : Fin (orderedSuffix S R).card) :
    ((S.orderIsoOfFin rfl).symm
      ⟨(orderedSuffix S R).orderEmbOfFin rfl i,
        (Finset.mem_filter.mp ((orderedSuffix S R).orderEmbOfFin_mem rfl i)).1⟩).val = R+i.val := by
  let T := orderedSuffix S R
  let v := T.orderEmbOfFin rfl i
  have hvT : v ∈ T := T.orderEmbOfFin_mem rfl i
  have hvR : R ≤ v.val := (Finset.mem_filter.mp hvT).2
  have hvS : v ∈ S := (Finset.mem_filter.mp hvT).1
  let j := (S.orderIsoOfFin rfl).symm ⟨v,hvS⟩
  have hj : S.orderEmbOfFin rfl j = v :=
    congrArg Subtype.val ((S.orderIsoOfFin rfl).apply_symm_apply _)
  have hr := orderEmb_rank S j
  rw [hj] at hr
  have he : (S.filter (fun x => x < v)).filter (fun x => x.val < R) =
      Finset.univ.filter (fun x => x.val < R) := by
    ext x
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · exact And.right
    · intro hx
      exact ⟨⟨hroot x hx,(show x.val < v.val from lt_of_lt_of_le hx hvR)⟩,hx⟩
  have hn : (S.filter (fun x => x < v)).filter (fun x => ¬ x.val < R) =
      T.filter (fun x => x < v) := by
    ext x
    simp only [T,orderedSuffix,Finset.mem_filter,Nat.not_lt]
    exact ⟨fun h => ⟨⟨h.1.1,h.2⟩,h.1.2⟩,fun h => ⟨⟨h.1.1,h.2⟩,h.1.2⟩⟩
  have hh := Finset.card_filter_add_card_filter_not
    (s := S.filter (fun x => x < v)) (fun x => x.val < R)
  rw [he,hn,Fin.card_filter_val_lt,Nat.min_eq_right hR,hr] at hh
  have ht := orderEmb_rank T i
  change (T.filter (fun x => x < v)).card = i.val at ht
  rw [ht] at hh
  exact hh.symm

def suffixFullIndex {N R : ℕ} (S : Finset (Fin N)) (hR : R ≤ N)
    (hroot : ∀ x : Fin N, x.val < R → x ∈ S)
    (i : Fin (orderedSuffix S R).card) : Fin S.card :=
  ⟨R+i.val,by rw [prefix_suffix_card S hR hroot]; omega⟩

lemma suffix_full_embedding {N R : ℕ} (S : Finset (Fin N)) (hR : R ≤ N)
    (hroot : ∀ x : Fin N, x.val < R → x ∈ S)
    (i : Fin (orderedSuffix S R).card) :
    S.orderEmbOfFin rfl (suffixFullIndex S hR hroot i) =
      (orderedSuffix S R).orderEmbOfFin rfl i := by
  have hh := suffix_full_rank S hR hroot i
  have he : (S.orderIsoOfFin rfl).symm
      ⟨(orderedSuffix S R).orderEmbOfFin rfl i,
        (Finset.mem_filter.mp ((orderedSuffix S R).orderEmbOfFin_mem rfl i)).1⟩ =
      suffixFullIndex S hR hroot i := Fin.ext hh
  rw [← he]
  exact congrArg Subtype.val ((S.orderIsoOfFin rfl).apply_symm_apply _)

end SharpTerminalLeave

end

end OAI
