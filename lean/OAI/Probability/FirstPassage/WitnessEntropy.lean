import OAI.Probability.FirstPassage.WitnessSelection
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union

namespace OAI

namespace PlanarFPP
open Finset

noncomputable def spatialNeighbors (i : ℤ×ℤ) : Finset (ℤ×ℤ) :=
  ((Icc (-3 : ℤ) 3) ×ˢ (Icc (-3 : ℤ) 3)).image (fun d => i+d)

lemma spatialNeighbors_card (i : ℤ×ℤ) : (spatialNeighbors i).card ≤ 49 := by
  apply (card_image_le).trans
  norm_num [card_product,Int.card_Icc,Int.toNat]

lemma mem_spatialNeighbors (i j : ℤ×ℤ) (h₁ : |j.1-i.1| ≤ 3) (h₂ : |j.2-i.2| ≤ 3) :
    j ∈ spatialNeighbors i := by
  apply mem_image.mpr
  refine ⟨j-i,?_,by abel⟩
  exact mem_product.mpr ⟨mem_Icc.mpr (abs_le.mp h₁),mem_Icc.mpr (abs_le.mp h₂)⟩

noncomputable def spatialItineraries (i : ℤ×ℤ) : ℕ → Finset (List (ℤ×ℤ))
  | 0 => {[]}
  | n+1 => (spatialNeighbors i).biUnion (fun j => (spatialItineraries j n).image (List.cons j))

lemma spatialItineraries_card (i : ℤ×ℤ) (n : ℕ) : (spatialItineraries i n).card ≤ 49^n := by
  induction n generalizing i with
  | zero => simp [spatialItineraries]
  | succ n ih =>
    calc
      _ ≤ ∑ j ∈ spatialNeighbors i, ((spatialItineraries j n).image (List.cons j)).card := card_biUnion_le
      _ ≤ ∑ _j ∈ spatialNeighbors i, 49^n := sum_le_sum (fun j _ => card_image_le.trans (ih j))
      _ = (spatialNeighbors i).card * 49^n := by simp
      _ ≤ 49*49^n := Nat.mul_le_mul_right _ (spatialNeighbors_card i)
      _ = _ := by rw [pow_succ]; omega

lemma mem_spatialItineraries (i : ℤ×ℤ) (is : List (ℤ×ℤ)) (h : BoundedIndexSteps i is) :
    is ∈ spatialItineraries i is.length := by
  induction is generalizing i with
  | nil => simp [spatialItineraries]
  | cons j js ih =>
    change j::js ∈ (spatialNeighbors i).biUnion (fun j => (spatialItineraries j js.length).image (List.cons j))
    change |j.1-i.1| ≤ 3 ∧ |j.2-i.2| ≤ 3 ∧ BoundedIndexSteps j js at h
    have hj : j ∈ spatialNeighbors i := mem_spatialNeighbors i j h.1 h.2.1
    have ht : js ∈ spatialItineraries j js.length := ih j h.2.2
    simp only [mem_biUnion,mem_image]
    exact ⟨j,hj,js,ht,rfl⟩

def increaseFirst : List ℕ → List ℕ
  | [] => []
  | n::ns => (n+1)::ns

noncomputable def compositionCandidates : ℕ → ℕ → Finset (List ℕ)
  | 0,t => {[t]}
  | n+1,0 => {List.replicate (n+2) 0}
  | n+1,t+1 => (compositionCandidates n (t+1)).image (List.cons 0) ∪
      (compositionCandidates (n+1) t).image increaseFirst
termination_by n t => n+t

lemma compositionCandidates_card (n t : ℕ) : (compositionCandidates n t).card ≤ 2^(n+t) := by
  induction n generalizing t with
  | zero => simp only [compositionCandidates,card_singleton,Nat.zero_add]; exact Nat.one_le_pow _ _ (by omega)
  | succ n ih =>
    induction t with
    | zero => simp only [compositionCandidates,card_singleton,Nat.add_zero]; exact Nat.one_le_pow _ _ (by omega)
    | succ t ht =>
      rw [compositionCandidates]
      calc
        _ ≤ ((compositionCandidates n (t+1)).image (List.cons 0)).card+
            ((compositionCandidates (n+1) t).image increaseFirst).card := card_union_le ..
        _ ≤ 2^(n+(t+1))+2^(n+1+t) := Nat.add_le_add (card_image_le.trans (ih _)) (card_image_le.trans ht)
        _ = 2^(n+1+(t+1)) := by rw [show n+(t+1)=n+1+t by omega,show n+1+(t+1)=(n+1+t)+1 by omega,pow_succ]; omega

lemma mem_compositionCandidates (n t : ℕ) (ns : List ℕ) (hlen : ns.length=n+1) (hsum : ns.sum=t) :
    ns ∈ compositionCandidates n t := by
  induction n generalizing t ns with
  | zero =>
    cases ns with
    | nil => simp at hlen
    | cons a ns =>
      have he : ns=[] := List.length_eq_zero_iff.mp (by simpa using hlen)
      subst ns
      have ha : a=t := by simpa using hsum
      simp [compositionCandidates,ha]
  | succ n ih =>
    induction t generalizing ns with
    | zero =>
      have hz : ns=List.replicate (n+2) 0 := by
        have zeros (ls : List ℕ) (hh : ls.sum=0) : ls=List.replicate ls.length 0 := by
          induction ls with
          | nil => rfl
          | cons a ls rec =>
            simp only [List.sum_cons] at hh
            have ha : a=0 := by omega
            have ht : ls.sum=0 := by omega
            simp only [List.length_cons,List.replicate_succ]
            exact congrArg₂ List.cons ha (rec ht)
        have he := zeros ns hsum
        simpa [hlen] using he
      simp [compositionCandidates,hz]
    | succ t ht =>
      cases ns with
      | nil => simp at hlen
      | cons a ns =>
        have hlen' : ns.length=n+1 := by simpa using hlen
        cases a with
        | zero =>
          rw [compositionCandidates]
          apply mem_union_left
          exact mem_image.mpr ⟨ns,ih (t+1) ns hlen' (by simpa using hsum),rfl⟩
        | succ a =>
          rw [compositionCandidates]
          apply mem_union_right
          exact mem_image.mpr ⟨a::ns,ht (a::ns) (by simpa using hlen) (by simp only [List.sum_cons] at hsum ⊢; omega),rfl⟩

noncomputable def compositionCover (n t : ℕ) : Finset (List ℕ) :=
  (compositionCandidates n t).filter (fun ns => ns.length=n+1 ∧ ns.sum=t)

lemma mem_compositionCover (n t : ℕ) (ns : List ℕ) :
    ns ∈ compositionCover n t ↔ ns.length=n+1 ∧ ns.sum=t := by
  simp only [compositionCover,mem_filter]
  exact ⟨fun h => h.2,fun h => ⟨mem_compositionCandidates n t ns h.1 h.2,h⟩⟩

lemma compositionCover_card (n t : ℕ) (ht : t ≤ n) : (compositionCover n t).card ≤ 4^n := by
  calc
    _ ≤ 2^(n+t) := (card_filter_le ..).trans (compositionCandidates_card n t)
    _ ≤ 2^(n+n) := Nat.pow_le_pow_right (by omega) (by omega)
    _ = 4^n := by rw [pow_add,← mul_pow]; norm_num

end PlanarFPP

end OAI
