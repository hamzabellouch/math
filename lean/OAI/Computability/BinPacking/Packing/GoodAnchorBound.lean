import OAI.Computability.BinPacking.Inventory.CurrentMatches
import OAI.Computability.BinPacking.Inventory.InventoryScores
import OAI.Computability.BinPacking.Inventory.LabelConservation

namespace OAI

noncomputable section

namespace BinPackingGap

open scoped BigOperators

variable {I : Instance} {b n : ℕ}

abbrev RoleItem (cls : I.Item → Subclass) (r : Role) :=
  {i : I.Item // (cls i).role = r}

theorem roleItem_label_count (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (r : Role)
    (roleLabel : RoleItem cls r → Fin n)
    (hspec : ∀ i, label i.val = some (roleLabel i)) (v : Fin n) :
    ((Finset.univ.filter fun i => roleLabel i = v).card : ℤ) =
      labelledRoleCount cls label r v := by
  classical
  have himage : (Finset.univ.filter fun i => roleLabel i = v).image Subtype.val =
      Finset.univ.filter (fun i => (cls i).role = r ∧ label i = some v) := by
    ext i
    constructor
    · intro hi
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
      have hv := (Finset.mem_filter.mp ha).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, a.property,
        (hspec a).trans (congrArg some hv)⟩
    · intro hi
      obtain ⟨hr, hv⟩ := (Finset.mem_filter.mp hi).2
      let a : RoleItem cls r := ⟨i, hr⟩
      have ha : roleLabel a = v := Option.some.inj ((hspec a).symm.trans hv)
      exact Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩, rfl⟩
  have hcard : (Finset.univ.filter fun i => roleLabel i = v).card =
      (Finset.univ.filter fun i => (cls i).role = r ∧ label i = some v).card := by
    rw [← himage, Finset.card_image_of_injective _ Subtype.val_injective]
  rw [hcard]
  simp [labelledRoleCount]

structure RoleLabelData (cls : I.Item → Subclass) (label : I.Item → Option (Fin n)) where
  row : RoleItem cls .x → Fin n
  anchor : RoleItem cls .anchor → Fin n
  localLabel : RoleItem cls .«local» → Fin n
  row_spec : ∀ i, label i.val = some (row i)
  anchor_spec : ∀ i, label i.val = some (anchor i)
  local_spec : ∀ i, label i.val = some (localLabel i)
  global_spec : ∀ i : RoleItem cls .«global», label i.val = none
  flag_spec : ∀ i : RoleItem cls .flag, label i.val = none

namespace RoleLabelData

theorem row_count {cls : I.Item → Subclass} {label : I.Item → Option (Fin n)}
    (L : RoleLabelData cls label) (v : Fin n) :
    ((Finset.univ.filter fun i => L.row i = v).card : ℤ) =
      labelledRoleCount cls label .x v :=
  roleItem_label_count cls label .x L.row L.row_spec v

theorem anchor_count {cls : I.Item → Subclass} {label : I.Item → Option (Fin n)}
    (L : RoleLabelData cls label) (v : Fin n) :
    ((Finset.univ.filter fun i => L.anchor i = v).card : ℤ) =
      labelledRoleCount cls label .anchor v :=
  roleItem_label_count cls label .anchor L.anchor L.anchor_spec v

theorem local_count {cls : I.Item → Subclass} {label : I.Item → Option (Fin n)}
    (L : RoleLabelData cls label) (v : Fin n) :
    ((Finset.univ.filter fun i => L.localLabel i = v).card : ℤ) =
      labelledRoleCount cls label .«local» v :=
  roleItem_label_count cls label .«local» L.localLabel L.local_spec v

def of_valid (cls : I.Item → Subclass) (label : I.Item → Option (Fin n))
    (hlabeled : ∀ i, (cls i).role = .x ∨ (cls i).role = .anchor ∨
      (cls i).role = .«local» → ∃ v, label i = some v)
    (hunlabeled : ∀ i, (cls i).role = .«global» ∨ (cls i).role = .flag →
      label i = none) : RoleLabelData cls label where
  row i := Classical.choose (hlabeled i.val (Or.inl i.property))
  anchor i := Classical.choose (hlabeled i.val (Or.inr (Or.inl i.property)))
  localLabel i := Classical.choose (hlabeled i.val (Or.inr (Or.inr i.property)))
  row_spec i := Classical.choose_spec (hlabeled i.val (Or.inl i.property))
  anchor_spec i := Classical.choose_spec (hlabeled i.val (Or.inr (Or.inl i.property)))
  local_spec i := Classical.choose_spec (hlabeled i.val (Or.inr (Or.inr i.property)))
  global_spec i := hunlabeled i.val (Or.inl i.property)
  flag_spec i := hunlabeled i.val (Or.inr i.property)

end RoleLabelData

namespace Packing

def roleItemAt (p : Packing I b) (cls : I.Item → Subclass) (r : Role)
    (t : p.TableBin cls) : RoleItem cls r :=
  ⟨p.itemAtRole cls t r, p.itemAtRole_role cls t r⟩

theorem roleItemAt_injective (p : Packing I b) (cls : I.Item → Subclass) (r : Role) :
    Function.Injective (p.roleItemAt cls r) := by
  intro t u h
  exact p.itemAtRole_injective cls r (congrArg Subtype.val h)

theorem roleItemAt_labels (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (L : RoleLabelData cls label)
    (t : p.TableBin cls) (r : Role) :
    label (p.itemAtRole cls t r) = tableRoleLabel
      (L.row (p.roleItemAt cls .x t))
      (L.localLabel (p.roleItemAt cls .«local» t))
      (L.anchor (p.roleItemAt cls .anchor t)) r := by
  cases r with
  | x => exact L.row_spec (p.roleItemAt cls .x t)
  | anchor => exact L.anchor_spec (p.roleItemAt cls .anchor t)
  | «global» => exact L.global_spec (p.roleItemAt cls .«global» t)
  | «local» => exact L.local_spec (p.roleItemAt cls .«local» t)
  | flag => exact L.flag_spec (p.roleItemAt cls .flag t)

theorem roleItemAt_labels_le (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (L : RoleLabelData cls label)
    (coordinate : I.Item → ℚ)
    (hsize : ∀ i, I.size i = encodedSize (cls i) (label i) (coordinate i))
    (hw : ∀ i, |coordinate i| ≤ 6) (t : p.TableBin cls) :
    L.row (p.roleItemAt cls .x t) ≤ L.anchor (p.roleItemAt cls .anchor t) ∧
      L.localLabel (p.roleItemAt cls .«local» t) ≤ L.anchor (p.roleItemAt cls .anchor t) :=
  p.table_labels_le_anchor cls label coordinate hsize hw t _ _ _
    (p.roleItemAt_labels cls label L t)

theorem outside_roleItems_image_subset (p : Packing I b) (cls : I.Item → Subclass)
    (r : Role) :
    (LabelConservation.outsideItems (p.roleItemAt cls r)).image Subtype.val ⊆
      p.outsideTableItems cls := by
  classical
  intro i hi
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  intro ht
  have haout := (Finset.mem_sdiff.mp ha).2
  apply haout
  let t : p.TableBin cls := ⟨p.assignment a.val, ht⟩
  refine Finset.mem_image.mpr ⟨t, Finset.mem_univ _, ?_⟩
  apply Subtype.ext
  exact p.itemAtRole_eq_of_mem cls t r a.val (p.mem_own_bin a.val) a.property

theorem outside_roleItems_card_le (p : Packing I b) (cls : I.Item → Subclass) (r : Role) :
    (LabelConservation.outsideItems (p.roleItemAt cls r)).card ≤
      (p.outsideTableItems cls).card := by
  classical
  rw [← Finset.card_image_of_injective
    (LabelConservation.outsideItems (p.roleItemAt cls r)) Subtype.val_injective]
  exact Finset.card_le_card (p.outside_roleItems_image_subset cls r)

end Packing

namespace Coverage

theorem goodTuplesAt_iff_roleLabels (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (L : RoleLabelData cls label)
    (v : Fin n) (t : p.TableBin cls) :
    t ∈ goodTuplesAt p cls label v ↔
      L.anchor (p.roleItemAt cls .anchor t) = v ∧
        L.row (p.roleItemAt cls .x t) = v ∧
          L.localLabel (p.roleItemAt cls .«local» t) = v := by
  rw [mem_goodTuplesAt]
  have hx := L.row_spec (p.roleItemAt cls .x t)
  have ha := L.anchor_spec (p.roleItemAt cls .anchor t)
  have hd := L.local_spec (p.roleItemAt cls .«local» t)
  change label (p.itemAtRole cls t .x) = some _ at hx
  change label (p.itemAtRole cls t .anchor) = some _ at ha
  change label (p.itemAtRole cls t .«local») = some _ at hd
  simp only [Packing.IsGoodTableBin, hx, ha, hd, Option.some.injEq]
  constructor
  · rintro ⟨⟨hr, hl⟩, hv⟩
    exact ⟨hv, hr.trans hv, hl.trans hv⟩
  · rintro ⟨hv, hr, hl⟩
    exact ⟨⟨hr.trans hv.symm, hl.trans hv.symm⟩, hv⟩

def badRoleAnchors (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (L : RoleLabelData cls label) (v : Fin n) :
    Finset (RoleItem cls .anchor) := by
  classical
  exact LabelConservation.badAnchors L.anchor L.row L.localLabel
    (p.roleItemAt cls .anchor) (p.roleItemAt cls .x) (p.roleItemAt cls .«local») v

theorem mem_badRoleAnchors (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (L : RoleLabelData cls label)
    (v : Fin n) (a : RoleItem cls .anchor) :
    a ∈ badRoleAnchors p cls label L v ↔ L.anchor a = v ∧
      ¬ ∃ t, p.roleItemAt cls .anchor t = a ∧
        L.row (p.roleItemAt cls .x t) = v ∧
          L.localLabel (p.roleItemAt cls .«local» t) = v := by
  classical
  exact LabelConservation.mem_badAnchors_iff L.anchor L.row L.localLabel
    (p.roleItemAt cls .anchor) (p.roleItemAt cls .x) (p.roleItemAt cls .«local»)
    (p.roleItemAt_injective cls .anchor) v a

theorem badRoleAnchors_image_eq (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (L : RoleLabelData cls label) (v : Fin n) :
    (badRoleAnchors p cls label L v).image Subtype.val = badAnchorsAt p cls label v := by
  classical
  ext i
  constructor
  · intro hi
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨hv, hnot⟩ := (mem_badRoleAnchors p cls label L v a).mp ha
    apply (mem_badAnchorsAt p cls label v a.val).mpr
    refine ⟨(mem_anchorItemsAt cls label v a.val).mpr ⟨a.property, ?_⟩, ?_⟩
    · rw [L.anchor_spec, hv]
    · intro hgood
      obtain ⟨t, ht, hat⟩ := Finset.mem_image.mp hgood
      obtain ⟨_, hr, hd⟩ := (goodTuplesAt_iff_roleLabels p cls label L v t).mp ht
      exact hnot ⟨t, Subtype.ext hat, hr, hd⟩
  · intro hi
    obtain ⟨hiA, hiBad⟩ := (mem_badAnchorsAt p cls label v i).mp hi
    obtain ⟨hr, hv⟩ := (mem_anchorItemsAt cls label v i).mp hiA
    let a : RoleItem cls .anchor := ⟨i, hr⟩
    have hva : L.anchor a = v := Option.some.inj ((L.anchor_spec a).symm.trans hv)
    refine Finset.mem_image.mpr ⟨a, ?_, rfl⟩
    apply (mem_badRoleAnchors p cls label L v a).mpr
    refine ⟨hva, ?_⟩
    rintro ⟨t, hat, hrow, hlocal⟩
    apply hiBad
    refine Finset.mem_image.mpr ⟨t, ?_, congrArg Subtype.val hat⟩
    apply (goodTuplesAt_iff_roleLabels p cls label L v t).mpr
    exact ⟨by simpa only [hat] using hva, hrow, hlocal⟩

@[simp] theorem badRoleAnchors_card (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (L : RoleLabelData cls label) (v : Fin n) :
    (badRoleAnchors p cls label L v).card = (badAnchorsAt p cls label v).card := by
  classical
  rw [← badRoleAnchors_image_eq p cls label L v,
    Finset.card_image_of_injective _ Subtype.val_injective]

variable (p : Packing I b) (cls : I.Item → Subclass)
variable (label : I.Item → Option (Fin n)) (L : RoleLabelData cls label)
variable (coordinate : I.Item → ℚ)
variable (hsize : ∀ i, I.size i = encodedSize (cls i) (label i) (coordinate i))
variable (hw : ∀ i, |coordinate i| ≤ 6) (B c : ℕ)
variable (hcard : I.n = 5 * B) (hb : b ≤ B + c)
variable (htotal : (∑ i, primaryScore (cls i)) = 0)
variable (hInvR : ∀ v, (Finset.univ.filter fun a => L.anchor a = v).card =
  (Finset.univ.filter fun r => L.row r = v).card)
variable (hInvD : ∀ v, (Finset.univ.filter fun a => L.anchor a = v).card =
  (Finset.univ.filter fun d => L.localLabel d = v).card)

include L coordinate hsize hw B hcard hb htotal hInvR hInvD

theorem badAnchorsAt_card_le (v : Fin n) :
    (badAnchorsAt p cls label v).card ≤
      3 * (25 * (c + 1) * (1 + 5 * primaryBound)) := by
  classical
  have hOutside := (p.outside_roleItems_card_le cls .anchor).trans
    (p.outsideTableItems_card_lt cls label coordinate hsize hw B c hcard hb htotal).le
  have hleR (t : p.TableBin cls) :
      (L.row (p.roleItemAt cls .x t)).val ≤
        (L.anchor (p.roleItemAt cls .anchor t)).val :=
    (p.roleItemAt_labels_le cls label L coordinate hsize hw t).1
  have hleD (t : p.TableBin cls) :
      (L.localLabel (p.roleItemAt cls .«local» t)).val ≤
        (L.anchor (p.roleItemAt cls .anchor t)).val :=
    (p.roleItemAt_labels_le cls label L coordinate hsize hw t).2
  have h := LabelConservation.badAnchors_card_le_three_mul L.anchor L.row L.localLabel
    (p.roleItemAt cls .anchor) (p.roleItemAt cls .x) (p.roleItemAt cls .«local»)
    (p.roleItemAt_injective cls .anchor) (p.roleItemAt_injective cls .x)
    (p.roleItemAt_injective cls .«local») hleR hleD hInvR hInvD
    (25 * (c + 1) * (1 + 5 * primaryBound)) hOutside v
  change (badRoleAnchors p cls label L v).card ≤ _ at h
  simpa only [badRoleAnchors_card] using h

theorem badAnchorsAt_subset_card_le (v : Fin n) (s : Finset I.Item)
    (hs : s ⊆ badAnchorsAt p cls label v) :
    s.card ≤ 3 * (25 * (c + 1) * (1 + 5 * primaryBound)) :=
  (Finset.card_le_card hs).trans
    (badAnchorsAt_card_le p cls label L coordinate hsize hw B c hcard hb htotal hInvR hInvD v)

theorem anchor_subset_loss_le (v : Fin n) (s : Finset I.Item)
    (hs : s ⊆ anchorItemsAt (I := I) cls label v) :
    (s \ roleItems p cls (goodTuplesAt p cls label v) .anchor).card ≤
      3 * (25 * (c + 1) * (1 + 5 * primaryBound)) := by
  apply badAnchorsAt_subset_card_le p cls label L coordinate hsize hw B c
    hcard hb htotal hInvR hInvD v
  intro i hi
  obtain ⟨his, hin⟩ := Finset.mem_sdiff.mp hi
  exact Finset.mem_sdiff.mpr ⟨hs his, hin⟩

theorem badAnchors_global_card_le :
    ((Finset.univ : Finset (Fin n)).biUnion (badAnchorsAt p cls label)).card ≤
      3 * n * (25 * (c + 1) * (1 + 5 * primaryBound)) := by
  classical
  calc
    _ ≤ ∑ v : Fin n, (badAnchorsAt p cls label v).card := Finset.card_biUnion_le
    _ ≤ ∑ _v : Fin n, 3 * (25 * (c + 1) * (1 + 5 * primaryBound)) := by
      apply Finset.sum_le_sum
      intro v _
      exact badAnchorsAt_card_le p cls label L coordinate hsize hw B c
        hcard hb htotal hInvR hInvD v
    _ = _ := by simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

end Coverage
end BinPackingGap

end

end OAI
