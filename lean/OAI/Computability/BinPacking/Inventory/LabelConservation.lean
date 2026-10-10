import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic

namespace OAI

namespace BinPackingGap
namespace FinitePrefixConservation

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

theorem remaining_eq_bad (keys good : Finset α) (resources : Finset β)
    (f : α → β) (hgood : good ⊆ keys)
    (hmap : ∀ x ∈ good, f x ∈ resources)
    (hinj : Set.InjOn f (good : Set α))
    (hcard : resources.card = keys.card) :
    (resources \ good.image f).card = (keys \ good).card := by
  have himage : good.image f ⊆ resources := Finset.image_subset_iff.mpr hmap
  rw [Finset.card_sdiff_of_subset himage, Finset.card_sdiff_of_subset hgood,
    Finset.card_image_of_injOn hinj, hcard]

theorem remaining_le_bad (keys good : Finset α) (resources remaining : Finset β)
    (f : α → β) (hgood : good ⊆ keys)
    (hmap : ∀ x ∈ good, f x ∈ resources)
    (hinj : Set.InjOn f (good : Set α))
    (hcard : resources.card = keys.card)
    (hremaining : remaining ⊆ resources \ good.image f) :
    remaining.card ≤ (keys \ good).card := by
  calc
    remaining.card ≤ (resources \ good.image f).card := Finset.card_le_card hremaining
    _ = (keys \ good).card := remaining_eq_bad keys good resources f hgood hmap hinj hcard

end FinitePrefixConservation

namespace LabelConservation

open scoped BigOperators

variable {n : ℕ}
variable {T A R D : Type*}
variable [Fintype T] [Fintype A] [Fintype R] [Fintype D]
variable [DecidableEq A] [DecidableEq R] [DecidableEq D]

def outsideItems (f : T → A) : Finset A := Finset.univ \ Finset.univ.image f

def prefixItems (label : A → Fin n) (h : ℕ) : Finset A :=
  Finset.univ.filter fun x => (label x).val < h

def prefixOutside (label : A → Fin n) (f : T → A) (h : ℕ) : Finset A :=
  (outsideItems f).filter fun x => (label x).val < h

def exports (labelA : A → Fin n) (labelR : R → Fin n)
    (anchor : T → A) (role : T → R) (h : ℕ) : Finset T :=
  Finset.univ.filter fun t =>
    (labelR (role t)).val < h ∧ ¬ (labelA (anchor t)).val < h

def labelDefects (labelA : A → Fin n) (labelR : R → Fin n)
    (anchor : T → A) (role : T → R) (v : Fin n) : Finset T :=
  Finset.univ.filter fun t => labelA (anchor t) = v ∧ labelR (role t) ≠ v

omit [DecidableEq A] in
@[simp] theorem prefixItems_zero (label : A → Fin n) : prefixItems label 0 = ∅ := by
  simp [prefixItems]

@[simp] theorem prefixOutside_zero (label : A → Fin n) (f : T → A) :
    prefixOutside label f 0 = ∅ := by
  simp [prefixOutside]

omit [Fintype A] [Fintype R] [DecidableEq A] [DecidableEq R] in
@[simp] theorem exports_zero (labelA : A → Fin n) (labelR : R → Fin n)
    (anchor : T → A) (role : T → R) : exports labelA labelR anchor role 0 = ∅ := by
  simp [exports]

omit [DecidableEq A] [DecidableEq R] in
theorem prefix_inventory_eq (labelA : A → Fin n) (labelR : R → Fin n)
    (hInv : ∀ v, (Finset.univ.filter fun a => labelA a = v).card =
      (Finset.univ.filter fun r => labelR r = v).card) (h : ℕ) :
    (prefixItems labelA h).card = (prefixItems labelR h).card := by
  let labels : Finset (Fin n) := Finset.univ.filter fun v => v.val < h
  have hA := Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset A)
    labels labelA
  have hR := Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset R)
    labels labelR
  have hsum : (∑ v ∈ labels, (Finset.univ.filter fun a => labelA a = v).card) =
      ∑ v ∈ labels, (Finset.univ.filter fun r => labelR r = v).card := by
    exact Finset.sum_congr rfl fun v _ => hInv v
  simpa only [labels, Finset.mem_filter, Finset.mem_univ, true_and, prefixItems]
    using hA.symm.trans (hsum.trans hR)

theorem outside_add_selected_eq (label : A → Fin n) (f : T → A)
    (hf : Function.Injective f) (h : ℕ) :
    (prefixOutside label f h).card + (prefixItems (label ∘ f) h).card =
      (prefixItems label h).card := by
  have hsplit := Finset.card_sdiff_add_card_inter
    (prefixItems label h) (Finset.univ.image f)
  have hout : prefixItems label h \ Finset.univ.image f = prefixOutside label f h := by
    ext x
    simp [prefixItems, prefixOutside, outsideItems, and_comm]
  have hin : prefixItems label h ∩ Finset.univ.image f =
      (Finset.univ.image f).filter (fun x => (label x).val < h) := by
    ext x
    simp [prefixItems, and_comm]
  rw [hout, hin, Finset.filter_image, Finset.card_image_of_injective _ hf] at hsplit
  simpa only [prefixItems, Function.comp_apply] using hsplit

omit [Fintype A] [Fintype R] [DecidableEq A] [DecidableEq R] in
theorem selected_add_exports_eq (labelA : A → Fin n) (labelR : R → Fin n)
    (anchor : T → A) (role : T → R)
    (hle : ∀ t, (labelR (role t)).val ≤ (labelA (anchor t)).val) (h : ℕ) :
    (prefixItems (labelA ∘ anchor) h).card + (exports labelA labelR anchor role h).card =
      (prefixItems (labelR ∘ role) h).card := by
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := prefixItems (labelR ∘ role) h) (fun t => (labelA (anchor t)).val < h)
  have hin : (prefixItems (labelR ∘ role) h).filter
      (fun t => (labelA (anchor t)).val < h) = prefixItems (labelA ∘ anchor) h := by
    ext t
    simp only [Finset.mem_filter, prefixItems, Finset.mem_univ, true_and,
      Function.comp_apply]
    exact ⟨fun ht => ht.2, fun ht => ⟨lt_of_le_of_lt (hle t) ht, ht⟩⟩
  have hout : (prefixItems (labelR ∘ role) h).filter
      (fun t => ¬ (labelA (anchor t)).val < h) = exports labelA labelR anchor role h := by
    ext t
    simp [prefixItems, exports]
  rw [hin, hout] at hsplit
  exact hsplit

theorem exports_add_outsideRole_eq_outsideAnchor
    (labelA : A → Fin n) (labelR : R → Fin n)
    (anchor : T → A) (role : T → R)
    (hAnchor : Function.Injective anchor) (hRole : Function.Injective role)
    (hle : ∀ t, (labelR (role t)).val ≤ (labelA (anchor t)).val)
    (hInv : ∀ v, (Finset.univ.filter fun a => labelA a = v).card =
      (Finset.univ.filter fun r => labelR r = v).card) (h : ℕ) :
    (exports labelA labelR anchor role h).card + (prefixOutside labelR role h).card =
      (prefixOutside labelA anchor h).card := by
  have hA := outside_add_selected_eq labelA anchor hAnchor h
  have hR := outside_add_selected_eq labelR role hRole h
  have hE := selected_add_exports_eq labelA labelR anchor role hle h
  have hI := prefix_inventory_eq labelA labelR hInv h
  omega

theorem exports_eq_outside_sub
    (labelA : A → Fin n) (labelR : R → Fin n)
    (anchor : T → A) (role : T → R)
    (hAnchor : Function.Injective anchor) (hRole : Function.Injective role)
    (hle : ∀ t, (labelR (role t)).val ≤ (labelA (anchor t)).val)
    (hInv : ∀ v, (Finset.univ.filter fun a => labelA a = v).card =
      (Finset.univ.filter fun r => labelR r = v).card) (h : ℕ) :
    ((exports labelA labelR anchor role h).card : ℤ) =
      (prefixOutside labelA anchor h).card - (prefixOutside labelR role h).card := by
  have hcon := exports_add_outsideRole_eq_outsideAnchor
    labelA labelR anchor role hAnchor hRole hle hInv h
  omega

theorem exports_card_le_outside
    (labelA : A → Fin n) (labelR : R → Fin n)
    (anchor : T → A) (role : T → R)
    (hAnchor : Function.Injective anchor) (hRole : Function.Injective role)
    (hle : ∀ t, (labelR (role t)).val ≤ (labelA (anchor t)).val)
    (hInv : ∀ v, (Finset.univ.filter fun a => labelA a = v).card =
      (Finset.univ.filter fun r => labelR r = v).card) (h : ℕ) :
    (exports labelA labelR anchor role h).card ≤ (outsideItems anchor).card := by
  have hcon := exports_add_outsideRole_eq_outsideAnchor
    labelA labelR anchor role hAnchor hRole hle hInv h
  have hout : (prefixOutside labelA anchor h).card ≤ (outsideItems anchor).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  omega

omit [Fintype A] [Fintype R] [DecidableEq A] [DecidableEq R] in
theorem labelDefects_subset_exports
    (labelA : A → Fin n) (labelR : R → Fin n)
    (anchor : T → A) (role : T → R)
    (hle : ∀ t, (labelR (role t)).val ≤ (labelA (anchor t)).val) (v : Fin n) :
    labelDefects labelA labelR anchor role v ⊆ exports labelA labelR anchor role v.val := by
  intro t ht
  obtain ⟨ha, hr⟩ := (Finset.mem_filter.mp ht).2
  have hl := hle t
  rw [ha] at hl
  have hn : (labelR (role t)).val ≠ v.val := fun he => hr (Fin.ext he)
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_, ?_⟩
  · omega
  · simp [ha]

theorem labelDefects_card_le_outside
    (labelA : A → Fin n) (labelR : R → Fin n)
    (anchor : T → A) (role : T → R)
    (hAnchor : Function.Injective anchor) (hRole : Function.Injective role)
    (hle : ∀ t, (labelR (role t)).val ≤ (labelA (anchor t)).val)
    (hInv : ∀ v, (Finset.univ.filter fun a => labelA a = v).card =
      (Finset.univ.filter fun r => labelR r = v).card) (v : Fin n) :
    (labelDefects labelA labelR anchor role v).card ≤ (outsideItems anchor).card := by
  exact (Finset.card_le_card (labelDefects_subset_exports labelA labelR anchor role hle v)).trans
    (exports_card_le_outside labelA labelR anchor role hAnchor hRole hle hInv v.val)

def badAnchors (labelA : A → Fin n) (labelR : R → Fin n) (labelD : D → Fin n)
    (anchor : T → A) (role : T → R) (localRole : T → D) (v : Fin n) : Finset A :=
  ((outsideItems anchor).filter fun a => labelA a = v) ∪
    (labelDefects labelA labelR anchor role v).image anchor ∪
    (labelDefects labelA labelD anchor localRole v).image anchor

omit [Fintype R] [Fintype D] [DecidableEq R] [DecidableEq D] in
theorem mem_badAnchors_iff
    (labelA : A → Fin n) (labelR : R → Fin n) (labelD : D → Fin n)
    (anchor : T → A) (role : T → R) (localRole : T → D)
    (hAnchor : Function.Injective anchor) (v : Fin n) (a : A) :
    a ∈ badAnchors labelA labelR labelD anchor role localRole v ↔
      labelA a = v ∧
        ¬ ∃ t, anchor t = a ∧ labelR (role t) = v ∧ labelD (localRole t) = v := by
  constructor
  · intro hbad
    rcases Finset.mem_union.mp hbad with hleft | hd
    · rcases Finset.mem_union.mp hleft with ho | hr
      · obtain ⟨hoa, hv⟩ := Finset.mem_filter.mp ho
        refine ⟨hv, ?_⟩
        rintro ⟨t, hat, _, _⟩
        exact (Finset.mem_sdiff.mp hoa).2
          (Finset.mem_image.mpr ⟨t, Finset.mem_univ _, hat⟩)
      · obtain ⟨t, ht, hat⟩ := Finset.mem_image.mp hr
        obtain ⟨hva, hvr⟩ := (Finset.mem_filter.mp ht).2
        refine ⟨by simpa only [hat] using hva, ?_⟩
        rintro ⟨u, hua, hur, _⟩
        have htu : t = u := hAnchor (hat.trans hua.symm)
        exact hvr (by simpa only [htu] using hur)
    · obtain ⟨t, ht, hat⟩ := Finset.mem_image.mp hd
      obtain ⟨hva, hvd⟩ := (Finset.mem_filter.mp ht).2
      refine ⟨by simpa only [hat] using hva, ?_⟩
      rintro ⟨u, hua, _, hud⟩
      have htu : t = u := hAnchor (hat.trans hua.symm)
      exact hvd (by simpa only [htu] using hud)
  · rintro ⟨hv, hnot⟩
    by_cases ha : a ∈ Finset.univ.image anchor
    · obtain ⟨t, _, hat⟩ := Finset.mem_image.mp ha
      have htv : labelA (anchor t) = v := by simpa only [hat] using hv
      by_cases hr : labelR (role t) = v
      · have hd : labelD (localRole t) ≠ v := fun hd => hnot ⟨t, hat, hr, hd⟩
        apply Finset.mem_union_right
        exact Finset.mem_image.mpr ⟨t, Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, htv, hd⟩, hat⟩
      · apply Finset.mem_union_left
        apply Finset.mem_union_right
        exact Finset.mem_image.mpr ⟨t, Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, htv, hr⟩, hat⟩
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ha⟩, hv⟩

theorem badAnchors_card_le_three_mul
    (labelA : A → Fin n) (labelR : R → Fin n) (labelD : D → Fin n)
    (anchor : T → A) (role : T → R) (localRole : T → D)
    (hAnchor : Function.Injective anchor) (hRole : Function.Injective role)
    (hLocal : Function.Injective localRole)
    (hleR : ∀ t, (labelR (role t)).val ≤ (labelA (anchor t)).val)
    (hleD : ∀ t, (labelD (localRole t)).val ≤ (labelA (anchor t)).val)
    (hInvR : ∀ v, (Finset.univ.filter fun a => labelA a = v).card =
      (Finset.univ.filter fun r => labelR r = v).card)
    (hInvD : ∀ v, (Finset.univ.filter fun a => labelA a = v).card =
      (Finset.univ.filter fun d => labelD d = v).card)
    (K : ℕ) (hOutside : (outsideItems anchor).card ≤ K) (v : Fin n) :
    (badAnchors labelA labelR labelD anchor role localRole v).card ≤ 3 * K := by
  have hR := labelDefects_card_le_outside labelA labelR anchor role hAnchor hRole hleR hInvR v
  have hD := labelDefects_card_le_outside labelA labelD anchor localRole
    hAnchor hLocal hleD hInvD v
  have hO : ((outsideItems anchor).filter fun a => labelA a = v).card ≤
      (outsideItems anchor).card := Finset.card_le_card (Finset.filter_subset _ _)
  have hRi := Finset.card_image_le (s := labelDefects labelA labelR anchor role v) (f := anchor)
  have hDi := Finset.card_image_le (s := labelDefects labelA labelD anchor localRole v)
    (f := anchor)
  have hU := Finset.card_union_le
    ((outsideItems anchor).filter fun a => labelA a = v)
    ((labelDefects labelA labelR anchor role v).image anchor)
  have hV := Finset.card_union_le
    (((outsideItems anchor).filter fun a => labelA a = v) ∪
      (labelDefects labelA labelR anchor role v).image anchor)
    ((labelDefects labelA labelD anchor localRole v).image anchor)
  unfold badAnchors
  omega

end LabelConservation
end BinPackingGap

end OAI
