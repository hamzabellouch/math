import OAI.NumberTheory.TwoPoint.Circuits.CircuitQueryWalk
import OAI.NumberTheory.TwoPoint.Circuits.CircuitRestrictionLaw

namespace OAI

/-! The switching encoding changes each queried block to the values that
satisfy its term. Query blocks are disjoint, so their responses can later be
restored without disturbing the remaining encoding. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

namespace DNFQueryBlock

lemma image_eq_outside {n : ℕ} (ρ : PartialAssignment n) (bs : List (DNFQueryBlock n))
    (i : Fin n) (hi : i ∉ support bs) : image ρ bs i = ρ i := by
  induction bs generalizing ρ with
  | nil => rfl
  | cons b bs ih =>
    have hb : i ∉ b.queried := fun hb => hi (mem_union_left _ hb)
    have ht : i ∉ support bs := fun ht => hi (mem_union_right _ ht)
    rw [image, ih _ ht]
    simp [PartialAssignment.assign, hb]

lemma image_extends {n : ℕ} (ρ : PartialAssignment n) (bs : List (DNFQueryBlock n))
    (h : support bs ⊆ ρ.free) : ρ.Extends (image ρ bs) := by
  intro i b hb
  have hi : i ∉ support bs := by
    intro hi
    have hn := (mem_filter.mp (h hi)).2
    rw [hb] at hn
    cases hn
  rw [image_eq_outside ρ bs i hi, hb]

lemma image_free {n : ℕ} (ρ : PartialAssignment n) (bs : List (DNFQueryBlock n)) :
    (image ρ bs).free = ρ.free \ support bs := by
  induction bs generalizing ρ with
  | nil => simp [image, support]
  | cons b bs ih =>
    rw [image, ih, PartialAssignment.free_assign, support]
    ext i
    simp only [mem_sdiff, mem_union]
    tauto

lemma image_assign_comm {n : ℕ} (ρ : PartialAssignment n) (bs : List (DNFQueryBlock n))
    (S : Finset (Fin n)) (hS : Disjoint S (support bs)) (x : BooleanCube n) :
    image (ρ.assign S x) bs = (image ρ bs).assign S x := by
  induction bs generalizing ρ with
  | nil => rfl
  | cons b bs ih =>
    have hh := disjoint_union_right.mp hS
    rw [image, PartialAssignment.assign_comm ρ S b.queried hh.1, ih _ hh.2]
    rfl

lemma image_eq_assign {n : ℕ} (ρ : PartialAssignment n) (bs : List (DNFQueryBlock n)) :
    image ρ bs = ρ.assign (support bs) (fun i => (image ρ bs i).getD false) := by
  funext i
  by_cases hi : i ∈ support bs
  · have hn : image ρ bs i ≠ none := by
      intro hn
      have hf : i ∈ (image ρ bs).free := mem_filter.mpr ⟨mem_univ _, hn⟩
      rw [image_free] at hf
      exact (mem_sdiff.mp hf).2 hi
    cases hb : image ρ bs i with
    | none => exact False.elim (hn hb)
    | some b => simp [PartialAssignment.assign, hi, hb]
  · simp [PartialAssignment.assign, hi, image_eq_outside ρ bs i hi]

lemma image_compatible {n : ℕ} (C : CubeTerm n) (ρ : PartialAssignment n)
    (bs : List (DNFQueryBlock n)) (hS : Disjoint C.support (support bs))
    (hC : C.Compatible ρ) : C.Compatible (image ρ bs) := by
  intro i hi
  have hn : i ∉ support bs := fun hs => Finset.disjoint_left.mp hS hi hs
  rw [image_eq_outside ρ bs i hn]
  exact hC i hi

end DNFQueryBlock

namespace CanonicalDNFWalk

lemma image_extends {n : ℕ} {F : List (CubeTerm n)} {ρ : PartialAssignment n}
    {bs : List (DNFQueryBlock n)} (h : CanonicalDNFWalk F ρ bs) :
    ρ.Extends (DNFQueryBlock.image ρ bs) :=
  DNFQueryBlock.image_extends ρ bs h.support_subset_free

lemma step_image_compatible {n : ℕ} {C : CubeTerm n} {F : List (CubeTerm n)}
    {ρ : PartialAssignment n} {bs : List (DNFQueryBlock n)}
    (x : BooleanCube n) (hC : C.Compatible ρ)
    (h : CanonicalDNFWalk F (ρ.assign (C.live ρ) x) bs) :
    C.Compatible (DNFQueryBlock.image ρ (⟨C, C.live ρ, x⟩ :: bs)) := by
  have hd : Disjoint C.support (DNFQueryBlock.support bs) := by
    apply Finset.disjoint_left.mpr
    intro i hi ht
    exact Finset.disjoint_left.mp (C.live_update_disjoint ρ x) hi
      (h.support_subset_free ht)
  apply DNFQueryBlock.image_compatible C _ bs hd
  intro i hi
  exact Or.inr (C.satisfied_assign_value ρ hC i hi)

lemma step_image_restore {n : ℕ} {C : CubeTerm n} {F : List (CubeTerm n)}
    {ρ : PartialAssignment n} {bs : List (DNFQueryBlock n)}
    (x : BooleanCube n) (h : CanonicalDNFWalk F (ρ.assign (C.live ρ) x) bs) :
    (DNFQueryBlock.image ρ (⟨C, C.live ρ, x⟩ :: bs)).assign (C.live ρ) x =
      DNFQueryBlock.image (ρ.assign (C.live ρ) x) bs := by
  change (DNFQueryBlock.image (ρ.assign (C.live ρ) C.value) bs).assign (C.live ρ) x = _
  rw [← DNFQueryBlock.image_assign_comm _ bs _ (head_disjoint_tail x h)]
  congr 1
  funext i
  by_cases hi : i ∈ C.live ρ <;> simp [PartialAssignment.assign, hi]

theorem image_weight {n : ℕ} {F : List (CubeTerm n)} {ρ : PartialAssignment n}
    {bs : List (DNFQueryBlock n)} (h : CanonicalDNFWalk F ρ bs)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p < 1) :
    (restrictionLaw n p hp hp1.le).weight ρ =
      (2 * p / (1 - p)) ^ DNFQueryBlock.length bs *
        (restrictionLaw n p hp hp1.le).weight (DNFQueryBlock.image ρ bs) := by
  have hw := restrictionLaw_assign_weight p hp hp1 ρ (DNFQueryBlock.support bs)
    h.support_subset_free (fun i => (DNFQueryBlock.image ρ bs i).getD false)
  rw [← DNFQueryBlock.image_eq_assign, ← h.length_eq_card_support] at hw
  exact hw

end CanonicalDNFWalk

end TwoPointCorrelations

end OAI
