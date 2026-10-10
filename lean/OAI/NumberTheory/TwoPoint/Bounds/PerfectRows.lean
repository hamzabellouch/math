import OAI.NumberTheory.TwoPoint.Bounds.OccurrenceCounts

namespace OAI

/-! The imperfect-row budget comes from actual singleton and unlit slots. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

variable {ι τ : Type*} [Fintype ι] [Fintype τ] [DecidableEq ι]

lemma singleton_slot_count (label : τ → ι) :
    (univ.filter (fun t : τ => label t ∈ singletonLabels label)).card =
      (singletonLabels label).card := by
  have hf := sum_card_fiberwise_eq_card_filter (univ : Finset τ) (singletonLabels label) label
  have hs : (∑ i ∈ singletonLabels label, (labelOccurrences label i).card) =
      (singletonLabels label).card := by
    calc
      _ = ∑ _i ∈ singletonLabels label, 1 := by
        apply sum_congr rfl
        intro i hi
        exact (mem_filter.mp hi).2
      _ = _ := by simp
  exact hf.symm.trans hs

omit [Fintype ι] in
lemma unlit_slot_count (label : τ → ι) (lit : τ → Bool) (S : Finset ι) :
    (univ.filter (fun t : τ => label t ∈ S ∧ lit t = false)).card =
      ∑ i ∈ S, (unlitOccurrences label lit i).card := by
  have hf := sum_card_fiberwise_eq_card_filter
    (univ.filter (fun t : τ => lit t = false)) S label
  have he (i : ι) :
      ((univ.filter (fun t : τ => lit t = false)).filter (fun t => label t = i)) =
        unlitOccurrences label lit i := by
    ext t
    simp [unlitOccurrences, labelOccurrences, and_comm]
  simp only [he] at hf
  rw [hf]
  congr 1
  ext t
  simp [and_comm]

variable {n J : ℕ}

/-- Every slot in a perfect row is lit and belongs to a nonsingleton label. -/
def PerfectRow (label : Fin n × Fin J → ι) (lit : Fin n × Fin J → Bool)
    (r : Fin n) : Prop :=
  ∀ j, label (r, j) ∈ nonsingletonLabels label ∧ lit (r, j) = true

/-- Charge a bad row to one singleton slot or one unlit nonsingleton slot.
The image under the row projection can only decrease cardinality. -/
theorem imperfect_rows_le_singletons_add_unlit (label : Fin n × Fin J → ι)
    (lit : Fin n × Fin J → Bool) :
    (univ.filter (fun r : Fin n => ¬PerfectRow label lit r)).card ≤
      (singletonLabels label).card +
        ∑ i : nonsingletonLabels label, (unlitOccurrences label lit i.val).card := by
  classical
  let A := univ.filter (fun t : Fin n × Fin J => label t ∈ singletonLabels label)
  let B := univ.filter (fun t : Fin n × Fin J =>
    label t ∈ nonsingletonLabels label ∧ lit t = false)
  have hsub : (univ.filter (fun r : Fin n => ¬PerfectRow label lit r)) ⊆
      A.image Prod.fst ∪ B.image Prod.fst := by
    intro r hr
    have hbad := (mem_filter.mp hr).2
    obtain ⟨j, hj⟩ : ∃ j, ¬(label (r, j) ∈ nonsingletonLabels label ∧ lit (r, j) = true) := by
      simpa only [PerfectRow, not_forall] using hbad
    by_cases hns : label (r, j) ∈ nonsingletonLabels label
    · have hlit : lit (r, j) = false := by
        cases hval : lit (r, j) <;> simp_all
      exact mem_union_right _ (mem_image.mpr ⟨(r, j), mem_filter.mpr ⟨mem_univ _, hns, hlit⟩, rfl⟩)
    · have hpos : 0 < (labelOccurrences label (label (r, j))).card :=
        card_pos.mpr ⟨(r, j), mem_filter.mpr ⟨mem_univ _, rfl⟩⟩
      have hlt : ¬2 ≤ (labelOccurrences label (label (r, j))).card := by
        simpa only [nonsingletonLabels, mem_filter, mem_univ, true_and] using hns
      have hsingle : label (r, j) ∈ singletonLabels label :=
        mem_filter.mpr ⟨mem_univ _, by omega⟩
      exact mem_union_left _ (mem_image.mpr ⟨(r, j), mem_filter.mpr ⟨mem_univ _, hsingle⟩, rfl⟩)
  calc
    _ ≤ (A.image Prod.fst ∪ B.image Prod.fst).card := card_le_card hsub
    _ ≤ (A.image Prod.fst).card + (B.image Prod.fst).card := card_union_le _ _
    _ ≤ A.card + B.card := Nat.add_le_add (card_image_le) (card_image_le)
    _ = _ := by
      rw [show A.card = (singletonLabels label).card from singleton_slot_count label,
        show B.card = ∑ i ∈ nonsingletonLabels label, (unlitOccurrences label lit i).card from
          unlit_slot_count label lit (nonsingletonLabels label), ← sum_coe_sort]

end TwoPointCorrelations

end OAI
