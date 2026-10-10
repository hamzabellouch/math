import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Ring

namespace OAI

namespace RyserCoveringCounterexample.Incidence
noncomputable section
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]

def ratioSet (E : Finset F) : Finset F :=
  ((E - E) ×ˢ ((E - E).erase 0)).image (fun z => z.1 / z.2)

def dilateSum (E : Finset F) (c : F) : Finset F :=
  E + E.image (fun x => c * x)

theorem mem_dilateSum {E : Finset F} {c z : F} :
    z ∈ dilateSum E c ↔ ∃ x ∈ E, ∃ y ∈ E, x + c * y = z := by
  constructor
  · intro hz
    obtain ⟨x, hx, w, hw, hzw⟩ := Finset.mem_add.mp hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hw
    exact ⟨x, hx, y, hy, hzw⟩
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact Finset.mem_add.mpr ⟨x, hx, c * y, Finset.mem_image.mpr ⟨y, hy, rfl⟩, rfl⟩

theorem mem_ratioSet {E : Finset F} {c : F} :
    c ∈ ratioSet E ↔ ∃ x ∈ E, ∃ x' ∈ E, ∃ y ∈ E, ∃ y' ∈ E,
      y ≠ y' ∧ (x - x') / (y - y') = c := by
  constructor
  · intro hc
    obtain ⟨⟨u, v⟩, huv, huv_eq⟩ := Finset.mem_image.mp hc
    obtain ⟨hu, hv⟩ := Finset.mem_product.mp huv
    obtain ⟨hv0, hv⟩ := Finset.mem_erase.mp hv
    obtain ⟨x, hx, x', hx', rfl⟩ := Finset.mem_sub.mp hu
    obtain ⟨y, hy, y', hy', rfl⟩ := Finset.mem_sub.mp hv
    exact ⟨x, hx, x', hx', y, hy, y', hy', sub_ne_zero.mp hv0, huv_eq⟩
  · rintro ⟨x, hx, x', hx', y, hy, y', hy', hyy', hquot⟩
    apply Finset.mem_image.mpr
    refine ⟨(x - x', y - y'), Finset.mem_product.mpr ⟨?_, ?_⟩, hquot⟩
    · exact Finset.mem_sub.mpr ⟨x, hx, x', hx', rfl⟩
    · exact Finset.mem_erase.mpr ⟨sub_ne_zero.mpr hyy',
        Finset.mem_sub.mpr ⟨y, hy, y', hy', rfl⟩⟩

theorem mem_ratioSet_of_collision {E : Finset F} {c : F}
    {x y x' y' : F} (hx : x ∈ E) (hy : y ∈ E)
    (hx' : x' ∈ E) (hy' : y' ∈ E)
    (hne : (x, y) ≠ (x', y')) (heq : x + c * y = x' + c * y') :
    c ∈ ratioSet E := by
  have hyy' : y ≠ y' := by
    intro h
    apply hne
    apply Prod.ext
    · exact add_right_cancel (by simpa only [h] using heq)
    · exact h
  apply mem_ratioSet.mpr
  refine ⟨x', hx', x, hx, y, hy, y', hy', hyy', ?_⟩
  apply (div_eq_iff (sub_ne_zero.mpr hyy')).mpr
  calc
    x' - x = (x' + c * y') - (x + c * y') := by ring
    _ = (x + c * y) - (x + c * y') := by rw [heq]
    _ = c * (y - y') := by ring

theorem mem_ratioSet_of_dilateSum_card_lt {E : Finset F} {c : F}
    (hcard : (dilateSum E c).card < E.card ^ 2) : c ∈ ratioSet E := by
  have hcard' : (dilateSum E c).card < (E ×ˢ E).card := by
    simpa only [Finset.card_product, pow_two] using hcard
  obtain ⟨z, hz, z', hz', hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard'
      (f := fun z : F × F => z.1 + c * z.2) (by
        intro z hz
        have hzE := Finset.mem_product.mp hz
        exact mem_dilateSum.mpr ⟨z.1, hzE.1, z.2, hzE.2, rfl⟩)
  have hzE := Finset.mem_product.mp hz
  have hzE' := Finset.mem_product.mp hz'
  exact mem_ratioSet_of_collision hzE.1 hzE.2 hzE'.1 hzE'.2 hne heq

theorem zero_mem_ratioSet {E : Finset F} (hE : 2 ≤ E.card) :
    (0 : F) ∈ ratioSet E := by
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hE
  exact mem_ratioSet.mpr ⟨x, hx, x, hx, x, hx, y, hy, hxy, by simp⟩

theorem one_mem_ratioSet {E : Finset F} (hE : 2 ≤ E.card) :
    (1 : F) ∈ ratioSet E := by
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hE
  exact mem_ratioSet.mpr ⟨x, hx, y, hy, x, hx, y, hy, hxy,
    div_self (sub_ne_zero.mpr hxy)⟩

theorem neg_mem_ratioSet {E : Finset F} {c : F} (hc : c ∈ ratioSet E) :
    -c ∈ ratioSet E := by
  obtain ⟨x, hx, x', hx', y, hy, y', hy', hyy', hquot⟩ := mem_ratioSet.mp hc
  apply mem_ratioSet.mpr
  refine ⟨x', hx', x, hx, y, hy, y', hy', hyy', ?_⟩
  rw [← neg_sub x x', neg_div, hquot]

theorem inv_mem_ratioSet {E : Finset F} {c : F}
    (hE : 2 ≤ E.card) (hc : c ∈ ratioSet E) : c⁻¹ ∈ ratioSet E := by
  by_cases hc0 : c = 0
  · simpa only [hc0, inv_zero] using zero_mem_ratioSet hE
  obtain ⟨x, hx, x', hx', y, hy, y', hy', hyy', hquot⟩ := mem_ratioSet.mp hc
  have hxx' : x ≠ x' := by
    intro h
    apply hc0
    simpa only [h, sub_self, zero_div] using hquot.symm
  exact mem_ratioSet.mpr ⟨y, hy, y', hy', x, hx, x', hx', hxx',
    by simpa only [inv_div] using congrArg Inv.inv hquot⟩

def ratioSubfield (E : Finset F) (hE : 2 ≤ E.card)
    (hadd : ∀ r ∈ ratioSet E, ∀ r' ∈ ratioSet E,
      (dilateSum E (r + r')).card < E.card ^ 2)
    (hmul : ∀ r ∈ ratioSet E, ∀ r' ∈ ratioSet E,
      (dilateSum E (r * r')).card < E.card ^ 2) : Subfield F where
  carrier := (ratioSet E : Set F)
  zero_mem' := zero_mem_ratioSet hE
  one_mem' := one_mem_ratioSet hE
  add_mem' := fun hr hr' => mem_ratioSet_of_dilateSum_card_lt (hadd _ hr _ hr')
  mul_mem' := fun hr hr' => mem_ratioSet_of_dilateSum_card_lt (hmul _ hr _ hr')
  neg_mem' := fun hc => neg_mem_ratioSet hc
  inv_mem' := fun _ hc => inv_mem_ratioSet hE hc

@[simp] theorem mem_ratioSubfield (E : Finset F) (hE : 2 ≤ E.card)
    (hadd : ∀ r ∈ ratioSet E, ∀ r' ∈ ratioSet E,
      (dilateSum E (r + r')).card < E.card ^ 2)
    (hmul : ∀ r ∈ ratioSet E, ∀ r' ∈ ratioSet E,
      (dilateSum E (r * r')).card < E.card ^ 2) (x : F) :
    x ∈ ratioSubfield E hE hadd hmul ↔ x ∈ ratioSet E := Iff.rfl

theorem card_le_card_ratioSet {E : Finset F} (hE : 2 ≤ E.card) :
    E.card ≤ (ratioSet E).card := by
  obtain ⟨x₀, hx₀, x₁, hx₁, hne⟩ := Finset.one_lt_card.mp hE
  have hden : x₁ - x₀ ≠ 0 := sub_ne_zero.mpr hne.symm
  apply Finset.card_le_card_of_injOn (fun x => (x - x₀) / (x₁ - x₀))
  · intro x hx
    exact mem_ratioSet.mpr ⟨x, hx, x₀, hx₀, x₁, hx₁, x₀, hx₀, hne.symm, rfl⟩
  · intro x hx y hy heq
    have hd : x - x₀ = y - x₀ := (div_left_inj' hden).mp heq
    calc
      x = (x - x₀) + x₀ := (sub_add_cancel x x₀).symm
      _ = (y - x₀) + x₀ := by rw [hd]
      _ = y := sub_add_cancel y x₀

end
end RyserCoveringCounterexample.Incidence

end OAI
