import OAI.NumberTheory.TwoPoint.Bounds.PerfectRows
import OAI.NumberTheory.TwoPoint.Bounds.DesignationWeights

namespace OAI

/-! Literal lit/unlit slot sets and the reciprocal coefficient of an actual word. -/

namespace TwoPointCorrelations

open Finset

variable {ι τ : Type*} [Fintype ι] [Fintype τ] [DecidableEq ι]

def nonsingletonLitSlots (label : τ → ι) (lit : τ → Bool) : Finset τ :=
  univ.filter (fun t => label t ∈ nonsingletonLabels label ∧ lit t = true)

def nonsingletonUnlitSlots (label : τ → ι) (lit : τ → Bool) : Finset τ :=
  univ.filter (fun t => label t ∈ nonsingletonLabels label ∧ lit t = false)

lemma nonsingleton_lit_fiber (label : τ → ι) (lit : τ → Bool) (i : ι) :
    (nonsingletonLitSlots label lit).filter (fun t => label t = i) =
      if i ∈ nonsingletonLabels label then litOccurrences label lit i else ∅ := by
  classical
  ext t
  by_cases ht : label t = i <;> by_cases hi : i ∈ nonsingletonLabels label <;>
    simp [nonsingletonLitSlots, litOccurrences, labelOccurrences, ht, hi]

lemma nonsingleton_unlit_fiber (label : τ → ι) (lit : τ → Bool) (i : ι) :
    (nonsingletonUnlitSlots label lit).filter (fun t => label t = i) =
      if i ∈ nonsingletonLabels label then unlitOccurrences label lit i else ∅ := by
  classical
  ext t
  by_cases ht : label t = i <;> by_cases hi : i ∈ nonsingletonLabels label <;>
    simp [nonsingletonUnlitSlots, unlitOccurrences, labelOccurrences, ht, hi]

lemma singleton_not_nonsingleton (label : τ → ι) (i : ι)
    (hi : i ∈ singletonLabels label) : i ∉ nonsingletonLabels label := by
  have hc := (mem_filter.mp hi).2
  simp only [nonsingletonLabels, mem_filter, mem_univ, true_and, hc]
  omega

lemma nonsingleton_of_used_not_singleton (label : τ → ι) (i : ι)
    (hused : 0 < (labelOccurrences label i).card) (hi : i ∉ singletonLabels label) :
    i ∈ nonsingletonLabels label := by
  have hn : (labelOccurrences label i).card ≠ 1 := by
    simpa only [singletonLabels, mem_filter, mem_univ, true_and] using hi
  exact mem_filter.mpr ⟨mem_univ _, by omega⟩

/-- The literal number of unlit nonsingleton slots is the sum of their
per-label occurrence counts, without charging singleton slots. -/
lemma nonsingleton_unlit_card (label : τ → ι) (lit : τ → Bool) :
    (nonsingletonUnlitSlots label lit).card =
      ∑ i : nonsingletonLabels label, (unlitOccurrences label lit i.val).card := by
  rw [nonsingletonUnlitSlots, unlit_slot_count]
  exact (sum_coe_sort _ _).symm

/-- On actual observed labels, the designated coefficient has one basic
reciprocal per prime and the exact extra powers from the nonsingletons. -/
theorem actual_designation_reciprocal_bound (label : τ → ι) (lit : τ → Bool)
    (hused : ∀ i, 0 < (labelOccurrences label i).card)
    (p : ι → ℝ) (H : ℝ) (hH : 0 < H) (hp : ∀ i, H ≤ p i) :
    (∏ t ∈ nonsingletonUnlitSlots label lit, (p (label t))⁻¹) *
      (∏ i ∈ (nonsingletonLitSlots label lit).image label, (p i)⁻¹) *
      (∏ i ∈ singletonLabels label, (p i)⁻¹) ≤
        (∏ i, (p i)⁻¹) * H⁻¹ ^
          (∑ i : nonsingletonLabels label,
            extraReciprocalExponent (litOccurrences label lit i.val).card
              (unlitOccurrences label lit i.val).card) := by
  classical
  have hzero (i : ι) (hi : i ∈ singletonLabels label) :
      ((nonsingletonLitSlots label lit).filter (fun t => label t = i)).card = 0 ∧
      ((nonsingletonUnlitSlots label lit).filter (fun t => label t = i)).card = 0 := by
    simp only [nonsingleton_lit_fiber, nonsingleton_unlit_fiber,
      ite_eq_right (singleton_not_nonsingleton label i hi), card_empty, and_self]
  have hm (i : ι) (hi : i ∉ singletonLabels label) :
      2 ≤ ((nonsingletonLitSlots label lit).filter (fun t => label t = i)).card +
        ((nonsingletonUnlitSlots label lit).filter (fun t => label t = i)).card := by
    have hns := nonsingleton_of_used_not_singleton label i (hused i) hi
    simp only [nonsingleton_lit_fiber, nonsingleton_unlit_fiber, ite_eq_left hns]
    rw [lit_unlit_count]
    exact (mem_filter.mp hns).2
  have hs : (∑ i, extraReciprocalExponent
      ((nonsingletonLitSlots label lit).filter (fun t => label t = i)).card
      ((nonsingletonUnlitSlots label lit).filter (fun t => label t = i)).card) =
      ∑ i : nonsingletonLabels label,
        extraReciprocalExponent (litOccurrences label lit i.val).card
          (unlitOccurrences label lit i.val).card := by
    calc
      _ = ∑ i ∈ nonsingletonLabels label, extraReciprocalExponent
          ((nonsingletonLitSlots label lit).filter (fun t => label t = i)).card
          ((nonsingletonUnlitSlots label lit).filter (fun t => label t = i)).card := by
        apply (sum_subset (subset_univ _) ?_).symm
        intro i _ hi
        simp [nonsingleton_lit_fiber, nonsingleton_unlit_fiber, hi,
          extraReciprocalExponent, litReciprocalExponent]
      _ = ∑ i ∈ nonsingletonLabels label,
          extraReciprocalExponent (litOccurrences label lit i).card
            (unlitOccurrences label lit i).card := by
        apply sum_congr rfl
        intro i hi
        simp only [nonsingleton_lit_fiber, nonsingleton_unlit_fiber, ite_eq_left hi]
      _ = _ := (sum_coe_sort _ _).symm
  simpa only [hs] using designated_all_reciprocal_bound (singletonLabels label)
    (nonsingletonLitSlots label lit) (nonsingletonUnlitSlots label lit) label p H hzero hm hH hp

end TwoPointCorrelations

end OAI
