import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic

namespace OAI

namespace Balanced
open scoped _root_.Balanced

open Finset

theorem repetition_mono {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) {s t : Finset α} (hst : s ⊆ t) :
    s.card - (s.image f).card ≤ t.card - (t.image f).card := by
  have himg : t.image f ⊆ s.image f ∪ (t \ s).image f := by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
    by_cases has : a ∈ s
    · exact Finset.mem_union_left _ (Finset.mem_image_of_mem f has)
    · exact Finset.mem_union_right _
        (Finset.mem_image_of_mem f (Finset.mem_sdiff.mpr ⟨ha, has⟩))
  have hcard := Finset.card_le_card himg
  have hunion := Finset.card_union_le (s.image f) ((t \ s).image f)
  have hdiff := Finset.card_sdiff_of_subset hst
  have hdiffimg := Finset.card_image_le (s := t \ s) (f := f)
  have hsimg := Finset.card_image_le (s := s) (f := f)
  have htimg := Finset.card_image_le (s := t) (f := f)
  have hstcard := Finset.card_le_card hst
  omega

theorem exists_small_repetition_witness {α β : Type*}
    [DecidableEq α] [DecidableEq β] (f : α → β) (s : Finset α) (k : ℕ)
    (hk : k ≤ s.card - (s.image f).card) :
    ∃ t ⊆ s, t.card ≤ 2 * k ∧ t.card - (t.image f).card = k := by
  obtain ⟨r, hrs, hinj, himage⟩ :=
    Finset.exists_subset_injOn_image_eq_of_surjOn (s : Set α) (s.image f)
      (show Set.SurjOn f (s : Set α) (s.image f) from by
        intro b hb
        exact Finset.mem_image.mp hb)
  have hrs' : r ⊆ s := hrs
  have hrcard : r.card = (s.image f).card := by
    rw [← himage, Finset.card_image_of_injOn hinj]
  have hk' : k ≤ (s \ r).card := by
    rw [Finset.card_sdiff_of_subset hrs', hrcard]
    exact hk
  obtain ⟨w, hw, hwcard⟩ := Finset.exists_subset_card_eq hk'
  have hws : w ⊆ s := fun a ha => (Finset.mem_sdiff.mp (hw ha)).1
  have hsurj : Set.SurjOn f (r : Set α) (w.image f) := by
    intro b hb
    have hbs : b ∈ s.image f := Finset.image_subset_image hws hb
    rw [← himage] at hbs
    exact Finset.mem_image.mp hbs
  obtain ⟨r', hr'r, hinj', himage'⟩ :=
    Finset.exists_subset_injOn_image_eq_of_surjOn (r : Set α) (w.image f) hsurj
  have hr'r' : r' ⊆ r := hr'r
  have hdisj : Disjoint w r' := by
    apply Finset.disjoint_left.mpr
    intro a haw har
    exact (Finset.mem_sdiff.mp (hw haw)).2 (hr'r' har)
  have hrcard' : r'.card = (w.image f).card := by
    rw [← himage', Finset.card_image_of_injOn hinj']
  have hbound : r'.card ≤ k := by
    rw [hrcard', ← hwcard]
    exact Finset.card_image_le
  refine ⟨w ∪ r', Finset.union_subset hws (hr'r'.trans hrs'), ?_, ?_⟩
  · rw [Finset.card_union_of_disjoint hdisj, hwcard]
    omega
  · rw [Finset.card_union_of_disjoint hdisj, Finset.image_union, himage',
      Finset.union_self, hwcard, hrcard']
    omega

theorem image_snd_sigma {ι α : Type*} [DecidableEq α]
    (s : Finset ι) (A : ι → Finset α) :
    (s.sigma A).image (fun x => x.2) = s.biUnion A := by
  ext a
  simp only [Finset.mem_image, Finset.mem_sigma, Finset.mem_biUnion]
  constructor
  · rintro ⟨⟨i, x⟩, ⟨hi, hx⟩, rfl⟩
    exact ⟨i, hi, hx⟩
  · rintro ⟨i, hi, ha⟩
    exact ⟨⟨i, a⟩, ⟨hi, ha⟩, rfl⟩

theorem exists_small_family_reuse_witness {ι α : Type*}
    [DecidableEq ι] [DecidableEq α] (s : Finset ι) (A : ι → Finset α) (k : ℕ)
    (hk : k ≤ (∑ i ∈ s, (A i).card) - (s.biUnion A).card) :
    ∃ t ⊆ s, t.card ≤ 2 * k ∧
      k ≤ (∑ i ∈ t, (A i).card) - (t.biUnion A).card := by
  have hk' : k ≤ (s.sigma A).card -
      ((s.sigma A).image (fun x => x.2)).card := by
    simpa only [Finset.card_sigma, image_snd_sigma] using hk
  obtain ⟨w, hw, hwcard, hwreuse⟩ :=
    exists_small_repetition_witness (fun x : Sigma (fun _ : ι => α) => x.2)
      (s.sigma A) k hk'
  let t := w.image Sigma.fst
  have hts : t ⊆ s := by
    intro i hi
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hi
    exact (Finset.mem_sigma.mp (hw hx)).1
  have hwt : w ⊆ t.sigma A := by
    intro x hx
    exact Finset.mem_sigma.mpr
      ⟨Finset.mem_image_of_mem Sigma.fst hx, (Finset.mem_sigma.mp (hw hx)).2⟩
  refine ⟨t, hts, (Finset.card_image_le).trans hwcard, ?_⟩
  have hmono := repetition_mono (fun x : Sigma (fun _ : ι => α) => x.2) hwt
  rw [hwreuse, Finset.card_sigma, image_snd_sigma] at hmono
  exact hmono

theorem exists_six_tuple_reuse_witness {ι α : Type*}
    [DecidableEq ι] [DecidableEq α] (s : Finset ι) (A : ι → Finset α)
    (hfour : ∀ i ∈ s, (A i).card = 4)
    (hreuse : 3 ≤ 4 * s.card - (s.biUnion A).card) :
    ∃ t ⊆ s, t.card ≤ 6 ∧ 3 ≤ 4 * t.card - (t.biUnion A).card := by
  have hsum : (∑ i ∈ s, (A i).card) = 4 * s.card := by
    calc
      (∑ i ∈ s, (A i).card) = ∑ _i ∈ s, 4 :=
        Finset.sum_congr rfl hfour
      _ = 4 * s.card := by simp [Nat.mul_comm]
  obtain ⟨t, hts, htcard, htr⟩ :=
    exists_small_family_reuse_witness s A 3 (by simpa only [hsum] using hreuse)
  refine ⟨t, hts, htcard, ?_⟩
  have hsumt : (∑ i ∈ t, (A i).card) = 4 * t.card := by
    calc
      (∑ i ∈ t, (A i).card) = ∑ _i ∈ t, 4 :=
        Finset.sum_congr rfl (fun i hi => hfour i (hts hi))
      _ = 4 * t.card := by simp [Nat.mul_comm]
  simpa only [hsumt] using htr

end Balanced

end OAI
