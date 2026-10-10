import Mathlib.Data.Finset.Max
import OAI.Combinatorics.BalancedRyser.Probability.EqualityPatternOrdering

namespace OAI

namespace Balanced.Local.Timing

open scoped Classical

variable {b κ : ℕ}

def earlierTuples (rank : Fin b → ℕ) (i : Fin b) : Finset (Fin b) :=
  Finset.univ.filter (fun j => rank j < rank i)

theorem exists_first_class_use (P : EqualityPattern b κ) (rank : Fin b → ℕ)
    (c : Fin (4*b-κ)) :
    ∃ i : Fin b, ∃ j : Fin 4, P.classOf i j = c ∧
      c ∉ (earlierTuples rank i).biUnion P.classSet := by
  let S := Finset.univ.filter (fun i : Fin b => c ∈ P.classSet i)
  have hS : S.Nonempty := by
    obtain ⟨⟨i,j⟩, hij⟩ := P.everyClass c
    refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hij⟩
  obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image S rank hS
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hi).2
  refine ⟨i, j, hj, ?_⟩
  intro hc
  obtain ⟨r, hr, hcr⟩ := Finset.mem_biUnion.mp hc
  have hlt : rank r < rank i := (Finset.mem_filter.mp hr).2
  have hle := hmin r (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcr⟩)
  omega

theorem mem_earlier_classes_iff_first_use (P : EqualityPattern b κ)
    (rank : Fin b → ℕ) (c : Fin (4*b-κ)) (first i : Fin b)
    (hfirst : c ∈ P.classSet first)
    (hnew : c ∉ (earlierTuples rank first).biUnion P.classSet) :
    c ∈ (earlierTuples rank i).biUnion P.classSet ↔ rank first < rank i := by
  constructor
  · intro hc
    obtain ⟨r, hr, hcr⟩ := Finset.mem_biUnion.mp hc
    have hri : rank r < rank i := (Finset.mem_filter.mp hr).2
    by_contra hn
    apply hnew
    refine Finset.mem_biUnion.mpr ⟨r, ?_, hcr⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, by omega⟩
  · intro h
    exact Finset.mem_biUnion.mpr
      ⟨first, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, hfirst⟩

theorem exists_first_class_use_timing (P : EqualityPattern b κ)
    (rank : Fin b → ℕ) (hrank : Function.Injective rank)
    (c : Fin (4*b-κ)) (i : Fin b) (hnot : ∀ j, P.classOf i j ≠ c) :
    ∃ first : Fin b, ∃ j : Fin 4, P.classOf first j = c ∧
      c ∉ (earlierTuples rank first).biUnion P.classSet ∧
      (rank first < rank i ∨ rank i < rank first) := by
  obtain ⟨first, j, hc, hnew⟩ := exists_first_class_use P rank c
  refine ⟨first, j, hc, hnew, ?_⟩
  rcases lt_trichotomy (rank first) (rank i) with h | h | h
  · exact Or.inl h
  · have heq := hrank h
    exact False.elim (hnot j (heq ▸ hc))
  · exact Or.inr h

def rootsFirstRank (R : Finset (Fin b)) (i : Fin b) : ℕ :=
  if i ∈ R then i.val else b + i.val

theorem rootsFirstRank_injective (R : Finset (Fin b)) :
    Function.Injective (rootsFirstRank R) := by
  intro i j h
  by_cases hi : i ∈ R <;> by_cases hj : j ∈ R <;>
    simp only [rootsFirstRank, hi, hj, ite_true, ite_false] at h
  all_goals apply Fin.ext; omega

theorem rootsFirstRank_prefix (R : Finset (Fin b)) (i : Fin b) :
    earlierTuples (rootsFirstRank R) i ⊆ R ∨
      R ⊆ earlierTuples (rootsFirstRank R) i := by
  by_cases hi : i ∈ R
  · left
    intro j hj
    have hlt := (Finset.mem_filter.mp hj).2
    by_contra hn
    simp only [rootsFirstRank, hi, hn, ite_true, ite_false] at hlt
    omega
  · right
    intro j hj
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simp only [rootsFirstRank, hi, hj, ite_true, ite_false]
    omega

end Balanced.Local.Timing

end OAI
