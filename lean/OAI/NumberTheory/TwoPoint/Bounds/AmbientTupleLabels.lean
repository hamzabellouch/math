import OAI.NumberTheory.TwoPoint.Walks.TupleResidueLabels
import OAI.NumberTheory.TwoPoint.Bounds.ObservedReciprocalBound
import OAI.NumberTheory.TwoPoint.Walks.TuplePerfectRows

namespace OAI

/-! Actual tuple slots have the same equality pattern in the ambient prime pool and column coordinates. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma columnPrimeValue_injective {J : ℕ} {P : Fin J → Finset ℕ}
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) :
    Function.Injective (fun c : (j : Fin J) × P j => c.2.val) := by
  rintro ⟨j, p⟩ ⟨l, q⟩ hpq
  change p.val = q.val at hpq
  have hjl : j = l := by
    by_contra hne
    exact disjoint_left.mp (hdisjoint j l (Ne.symm hne)) p.property (hpq.symm ▸ q.property)
  subst l
  exact congrArg (Sigma.mk j) (Subtype.ext hpq)

lemma tuple_label_eq_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    {J R : ℕ} {P : Fin J → Finset ℕ} (w : ColumnPrimeAssignment J R P)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (p : ι → ℕ) (hinj : Function.Injective p) (label : Fin R × Fin J → ι)
    (hlabel : ∀ i j, p (label (i, j)) = (w j i).val) (t u : Fin R × Fin J) :
    label t = label u ↔ tupleSlotLabel w t = tupleSlotLabel w u := by
  rw [← hinj.eq_iff, ← (columnPrimeValue_injective hdisjoint).eq_iff]
  change p (label t) = p (label u) ↔ (w t.2 t.1).val = (w u.2 u.1).val
  rw [show p (label t) = (w t.2 t.1).val from hlabel t.1 t.2,
    show p (label u) = (w u.2 u.1).val from hlabel u.1 u.2]

lemma tuple_label_singletonSlots {ι : Type*} [Fintype ι] [DecidableEq ι]
    {J R : ℕ} {P : Fin J → Finset ℕ} (w : ColumnPrimeAssignment J R P)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (p : ι → ℕ) (hinj : Function.Injective p) (label : Fin R × Fin J → ι)
    (hlabel : ∀ i j, p (label (i, j)) = (w j i).val) :
    singletonSlots label = singletonSlots (tupleSlotLabel w) := by
  have he (t : Fin R × Fin J) : labelOccurrences label (label t) =
      labelOccurrences (tupleSlotLabel w) (tupleSlotLabel w t) := by
    ext u
    simp only [labelOccurrences, mem_filter, mem_univ, true_and]
    exact tuple_label_eq_iff w hdisjoint p hinj label hlabel u t
  ext t
  simp only [singletonSlots, singletonLabels, mem_filter, mem_univ, true_and, he]

lemma tuple_label_singleton_count {ι : Type*} [Fintype ι] [DecidableEq ι]
    {J R : ℕ} {P : Fin J → Finset ℕ} (w : ColumnPrimeAssignment J R P)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (p : ι → ℕ) (hinj : Function.Injective p) (label : Fin R × Fin J → ι)
    (hlabel : ∀ i j, p (label (i, j)) = (w j i).val) :
    (singletonLabels label).card = columnSingletonCount w := by
  calc
    _ = (singletonSlots label).card := (singleton_slot_count label).symm
    _ = (singletonSlots (tupleSlotLabel w)).card :=
      congrArg Finset.card (tuple_label_singletonSlots w hdisjoint p hinj label hlabel)
    _ = _ := (singleton_slot_count (tupleSlotLabel w)).trans (tupleSlotLabel_singletons w)

lemma tuple_label_perfectRows {ι : Type*} [Fintype ι] [DecidableEq ι]
    {J R : ℕ} {P : Fin J → Finset ℕ} (w : ColumnPrimeAssignment J R P)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (p : ι → ℕ) (hinj : Function.Injective p) (label : Fin R × Fin J → ι)
    (hlabel : ∀ i j, p (label (i, j)) = (w j i).val) (U : Finset (Fin R × Fin J)) :
    perfectRows label U = perfectRows (tupleSlotLabel w) U := by
  simp only [perfectRows, tuple_label_singletonSlots w hdisjoint p hinj label hlabel]

lemma tuple_label_reciprocal {ι : Type*} [Fintype ι] [DecidableEq ι]
    {J R : ℕ} {P : Fin J → Finset ℕ} (w : ColumnPrimeAssignment J R P)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (p : ι → ℕ) (hinj : Function.Injective p) (label : Fin R × Fin J → ι)
    (hlabel : ∀ i j, p (label (i, j)) = (w j i).val) :
    (∏ i ∈ univ.image label, (p i : ℝ)⁻¹) = columnReciprocalWeight w := by
  have he : (univ.image label).image p = tuplePrimeSupport w := by
    ext q
    simp only [mem_image, mem_univ, true_and, mem_tuplePrimeSupport]
    constructor
    · rintro ⟨i, ⟨t, rfl⟩, rfl⟩
      exact ⟨t.2, t.1, (hlabel t.1 t.2).symm⟩
    · rintro ⟨j, i, rfl⟩
      exact ⟨label (i, j), ⟨(i, j), rfl⟩, hlabel i j⟩
  rw [← tuplePrimeSupport_reciprocal w hdisjoint, ← he]
  exact (prod_image (g := p) (f := fun q : ℕ => (q : ℝ)⁻¹)
    (fun _ _ _ _ h => hinj h)).symm

theorem designatedReciprocal_le_tuple {ι : Type*} [Fintype ι] [DecidableEq ι]
    {J R : ℕ} {P : Fin J → Finset ℕ} (w : ColumnPrimeAssignment J R P)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (p : ι → ℕ) (hinj : Function.Injective p) (hp : ∀ i, 0 < p i)
    (label : Fin R × Fin J → ι)
    (hlabel : ∀ i j, p (label (i, j)) = (w j i).val)
    (U : Finset (Fin R × Fin J)) (hU : U ⊆ nonsingletonSlots label) :
    designatedReciprocal p (singletonLabels label) (nonsingletonSlots label \ U) U label ≤
      columnReciprocalWeight w := by
  have hb := full_word_designated_reciprocal_bound label U hU p 1
    (by norm_num) (fun i => by exact_mod_cast hp i)
  rw [designation_sdiff_decidable (fun a b => Classical.propDecidable (a = b))
    (inferInstance : DecidableEq (Fin R × Fin J)) _ _] at hb
  simpa only [inv_one, one_pow, mul_one, tuple_label_reciprocal w hdisjoint p hinj label hlabel]
    using hb

end TwoPointCorrelations

end OAI
