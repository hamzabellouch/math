import OAI.NumberTheory.TwoPoint.Walks.AttachedCatalogAvoidance

namespace OAI

/-! Equality of the finite residue-catalog indicator with the actual integer vertex mask. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma witnessAvoidance_eq_indicator {ι A W : Type*} [Fintype W]
    (I : W → (ι → A) → Bool) (x : ι → A) :
    witnessAvoidance I x = if ∀ w, I w x = false then 1 else 0 := by
  unfold witnessAvoidance
  split_ifs with hI
  · apply prod_eq_one
    intro w _
    simp only [hI w, Bool.false_eq_true, ite_false, sub_zero]
  · obtain ⟨w, hw⟩ := not_forall.mp hI
    have ht : I w x = true := Bool.eq_true_of_not_eq_false hw
    apply prod_eq_zero (mem_univ w)
    simp [ht]

lemma witnessAvoidance_eq_one_of_ne_zero {ι A W : Type*} [Fintype W]
    (I : W → (ι → A) → Bool) (x : ι → A) (hx : witnessAvoidance I x ≠ 0) :
    witnessAvoidance I x = 1 := by
  rw [witnessAvoidance_eq_indicator] at hx ⊢
  split_ifs with hI
  · rfl
  · simp [hI] at hx

theorem attachedCatalogAvoidance_eq_indicator {h J M : ℕ}
    (F : ProhibitedPrimeFamily h J M) (s B D : ℕ) (main : List SignedStep)
    (hD : main.length ≤ D) (x : ↥(F.P ∪ F.Q) → Fin B) (n : ℤ)
    (hn : ∀ p : ↥(F.P ∪ F.Q), (n : ZMod p.val) = ((x p).val : ZMod p.val)) :
    attachedCatalogAvoidance F s B D main x =
      if ∀ v ≤ main.length, ¬ProhibitedSite h s (fun d q => (d, q) ∈ F.pairs)
        (n + wordDisplacement h (main.take v)) then 1 else 0 := by
  split_ifs with hkeep
  · exact witnessAvoidance_eq_one_of_ne_zero _ x
      ((attachedCatalogAvoidance_ne_zero_iff F s B D main hD x n hn).mpr hkeep)
  · by_contra hne
    exact hkeep ((attachedCatalogAvoidance_ne_zero_iff F s B D main hD x n hn).mp hne)

theorem attachedCatalogAvoidance_eq_vertex_product {h J M : ℕ}
    (F : ProhibitedPrimeFamily h J M) (s B D : ℕ) (main : List SignedStep)
    (hD : main.length ≤ D) (x : ↥(F.P ∪ F.Q) → Fin B) (n : ℤ)
    (hn : ∀ p : ↥(F.P ∪ F.Q), (n : ZMod p.val) = ((x p).val : ZMod p.val)) :
    attachedCatalogAvoidance F s B D main x =
      ∏ v : Fin (main.length + 1),
        if ProhibitedSite h s (fun d q => (d, q) ∈ F.pairs)
          (n + wordDisplacement h (main.take v.val)) then (0 : ℝ) else 1 := by
  rw [attachedCatalogAvoidance_eq_indicator F s B D main hD x n hn]
  split_ifs with hkeep
  · symm
    apply prod_eq_one
    intro v _
    exact ite_eq_right (hkeep v.val (Nat.le_of_lt_succ v.isLt))
  · push Not at hkeep
    obtain ⟨v, hv, hbad⟩ := hkeep
    symm
    exact prod_eq_zero (mem_univ (⟨v, by omega⟩ : Fin (main.length + 1))) (ite_eq_left hbad)

theorem attachedCatalogAvoidance_eq_departure_product {h J M : ℕ}
    (F : ProhibitedPrimeFamily h J M) (s B D : ℕ) (main : List SignedStep)
    (hD : main.length ≤ D) (hlen : 0 < main.length) (hclosed : wordDisplacement h main = 0)
    (x : ↥(F.P ∪ F.Q) → Fin B) (n : ℤ)
    (hn : ∀ p : ↥(F.P ∪ F.Q), (n : ZMod p.val) = ((x p).val : ZMod p.val)) :
    attachedCatalogAvoidance F s B D main x =
      ∏ v : Fin main.length,
        if ProhibitedSite h s (fun d q => (d, q) ∈ F.pairs)
          (n + wordDisplacement h (main.take v.val)) then (0 : ℝ) else 1 := by
  have he : (∀ v ≤ main.length, ¬ProhibitedSite h s (fun d q => (d, q) ∈ F.pairs)
        (n + wordDisplacement h (main.take v))) ↔
      (∀ v < main.length, ¬ProhibitedSite h s (fun d q => (d, q) ∈ F.pairs)
        (n + wordDisplacement h (main.take v))) := by
    constructor
    · exact fun hh v hv => hh v hv.le
    · intro hh v hv
      rcases lt_or_eq_of_le hv with hv | rfl
      · exact hh v hv
      · simpa only [List.take_length, hclosed, add_zero, List.take_zero,
          wordDisplacement_nil] using hh 0 hlen
  rw [attachedCatalogAvoidance_eq_indicator F s B D main hD x n hn]
  simp only [he]
  split_ifs with hkeep
  · symm
    apply prod_eq_one
    intro v _
    exact ite_eq_right (hkeep v.val v.isLt)
  · push Not at hkeep
    obtain ⟨v, hv, hbad⟩ := hkeep
    symm
    exact prod_eq_zero (mem_univ (⟨v, hv⟩ : Fin main.length)) (ite_eq_left hbad)

end TwoPointCorrelations

end OAI
