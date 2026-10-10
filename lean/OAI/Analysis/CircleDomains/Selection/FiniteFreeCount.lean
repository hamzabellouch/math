import OAI.Analysis.CircleDomains.Selection.FiniteLevelAssembly

namespace OAI

/-! For a finite level intersection, equality with the counts in two
disjoint paid pieces leaves no additional free point.
-/

open Set Function
open scoped ENNReal Classical

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

theorem pathImageCount_eq_encard (H : Set X) (γ : C(PathTime, X)) :
    pathImageCount H γ = ((range γ ∩ H).encard : ℝ≥0∞) := by
  rw [pathImageCount, ← ENNReal.tsum_set_one,
    tsum_subtype (range γ ∩ H) (fun _ : X => (1 : ℝ≥0∞))]
  simp only [Set.indicator]

theorem pathImageCount_union_of_disjoint {A B : Set X} (hAB : Disjoint A B)
    (γ : C(PathTime, X)) :
    pathImageCount (A ∪ B) γ = pathImageCount A γ + pathImageCount B γ := by
  rw [pathImageCount, pathImageCount, pathImageCount, ← ENNReal.tsum_add]
  apply tsum_congr
  intro x
  have hh : ¬ (x ∈ A ∧ x ∈ B) := fun h => disjoint_left.mp hAB h.1 h.2
  by_cases hr : x ∈ range γ <;> by_cases ha : x ∈ A <;> by_cases hb : x ∈ B <;>
    simp_all only [mem_inter_iff, mem_union, ite_true, ite_false, and_true, and_false,
      or_true, or_false, add_zero, zero_add,
      not_true_eq_false, not_false_eq_true, and_self]

theorem no_free_hits_of_finite_count_le
    (U Flags H : Set X) (hdisj : Disjoint U Flags) (γ : C(PathTime, X))
    (hfinite : pathImageCount H γ < ∞)
    (hcount : pathImageCount H γ ≤ pathImageCount (U ∩ H) γ + pathImageCount (Flags ∩ H) γ) :
    ¬ ∃ x ∈ range γ ∩ (Uᶜ \ Flags), x ∈ H := by
  let A := range γ ∩ H
  let B := range γ ∩ ((U ∩ H) ∪ (Flags ∩ H))
  have hA : A.Finite := (pathImageCount_lt_top_iff H γ).mp hfinite
  have hBA : B ⊆ A := by
    rintro x ⟨hx, h | h⟩ <;> exact ⟨hx, h.2⟩
  have hbcount : pathImageCount H γ ≤ pathImageCount ((U ∩ H) ∪ (Flags ∩ H)) γ := by
    rw [pathImageCount_union_of_disjoint (hdisj.mono inter_subset_left inter_subset_left)]
    exact hcount
  have hcard : A.encard ≤ B.encard := by
    rw [pathImageCount_eq_encard, pathImageCount_eq_encard] at hbcount
    exact_mod_cast hbcount
  have heq : B = A := hA.eq_of_subset_of_encard_le' hBA hcard
  rintro ⟨x, ⟨hx, hu, hf⟩, hxH⟩
  have hxB : x ∈ B := heq.symm ▸ (show x ∈ A from ⟨hx, hxH⟩)
  rcases hxB.2 with h | h
  · exact hu h.1
  · exact hf h.1

end CircleDomainRigidity

end

end OAI
