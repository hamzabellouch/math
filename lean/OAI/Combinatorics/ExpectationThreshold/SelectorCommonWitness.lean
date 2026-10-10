import OAI.Combinatorics.ExpectationThreshold.SelectorDefinitionsLemmas
import OAI.Combinatorics.ExpectationThreshold.SelectorProfile
import OAI.Combinatorics.ExpectationThreshold.SelectorReconstruction
import OAI.Combinatorics.ExpectationThreshold.SelectorTruncation

namespace OAI

/-!
# One witness for an entire selector profile group

A nonempty group contains an actual selected move, hence an actual feasible
family member. Its admissibility tests depend on the original coloring only
through the full profile. Maximizing each cutoff for this one member therefore
produces common heavy sets for the entire group. Selected-move minimality puts
every moved row inside its corresponding common heavy set.
-/

noncomputable section

namespace TalagrandThreshold.Selector

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The same actual family member and cutoffs work for every original coloring
in a fixed final-coloring/profile group. -/
structure CommonWitness {F : Family α} (mu : MassFamily F) {s : ℕ}
    (z : Coloring α s) (n : Profile s) where
  member : ↥F
  cutoff : Fin s → ℝ
  admissible : ∀ a ∈ groupOriginals mu z n, ∀ i : Fin s,
    Admissible (mu.weight member) (prefixSet z i) (crossings a z i : ℝ)
      (dscale i) (cutoff i)
  maximal : ∀ (i : Fin s) (u : ℝ),
    Admissible (mu.weight member) (prefixSet z i) (profileCrossings n i : ℝ)
      (dscale i) u → u ≤ cutoff i
  card_le : ∀ i : Fin s,
    (heavySet (mu.weight member) (cutoff i)).card ≤ 2 ^ (i.val + 1) * profileSize n
  moved_subset : ∀ a ∈ groupOriginals mu z n, ∀ i : Fin s,
    movedRow a z i ⊆ heavySet (mu.weight member) (cutoff i)

omit [Fintype α] [DecidableEq α] in
private theorem card_le_profile_of_truncation {s : ℕ}
    (R : Finset α) (i : Fin s) (n : Profile s) (m : ℕ)
    (hcard : (R.card : ℝ) ≤ (m : ℝ) / dscale i)
    (hm : m ≤ profileSize n) :
    R.card ≤ 2 ^ (i.val + 1) * profileSize n := by
  have hreal : (R.card : ℝ) ≤ ((m * 2 ^ (i.val + 1) : ℕ) : ℝ) := by
    simpa only [dscale, div_inv_eq_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      using hcard
  have hnat : R.card ≤ m * 2 ^ (i.val + 1) := (Nat.cast_le (α := ℝ)).mp hreal
  calc
    R.card ≤ m * 2 ^ (i.val + 1) := hnat
    _ ≤ profileSize n * 2 ^ (i.val + 1) := Nat.mul_le_mul_right _ hm
    _ = 2 ^ (i.val + 1) * profileSize n := Nat.mul_comm _ _

/-- The common witness is constructed from the actual nonempty group; no
additional feasibility, reconstruction, or cardinality certificate is assumed. -/
theorem exists_common_witness {F : Family α} (mu : MassFamily F) {s : ℕ}
    (z : Coloring α s) (n : Profile s)
    (hne : (groupOriginals mu z n).Nonempty) : Nonempty (CommonWitness mu z n) := by
  classical
  obtain ⟨a₀, ha₀⟩ := hne
  have ha₀' := (mem_groupOriginals mu a₀ z n).mp ha₀
  obtain ⟨H₀, hminimal⟩ := ha₀'.2.1
  obtain ⟨H, hfeasible⟩ := hminimal.1.1.2
  have hcross₀ (i : Fin s) : crossings a₀ z i = profileCrossings n i := by
    rw [crossings_eq_profileCrossings, ha₀'.2.2]
  have hcutoff (i : Fin s) : ∃ ε : ℝ,
      Admissible (mu.weight H) (prefixSet z i) (profileCrossings n i : ℝ) (dscale i) ε ∧
      (∀ u, Admissible (mu.weight H) (prefixSet z i) (profileCrossings n i : ℝ)
        (dscale i) u → u ≤ ε) ∧
      ((heavySet (mu.weight H) ε).card : ℝ) ≤ (profileCrossings n i : ℝ) / dscale i := by
    apply exists_maximal_truncation_div (mu.weight H) (prefixSet z i)
      (profileCrossings n i : ℝ) (dscale i) (mu.nonneg H) (mu.total H)
      (Nat.cast_nonneg _) (dscale_pos i) (dscale_lt_one i)
    simpa only [hcross₀ i] using hfeasible i
  let ε : Fin s → ℝ := fun i => Classical.choose (hcutoff i)
  have hε (i : Fin s) :
      Admissible (mu.weight H) (prefixSet z i) (profileCrossings n i : ℝ) (dscale i) (ε i) ∧
      (∀ u, Admissible (mu.weight H) (prefixSet z i) (profileCrossings n i : ℝ)
        (dscale i) u → u ≤ ε i) ∧
      ((heavySet (mu.weight H) (ε i)).card : ℝ) ≤
        (profileCrossings n i : ℝ) / dscale i :=
    Classical.choose_spec (hcutoff i)
  have hadmissible : ∀ a ∈ groupOriginals mu z n, ∀ i : Fin s,
      Admissible (mu.weight H) (prefixSet z i) (crossings a z i : ℝ) (dscale i) (ε i) := by
    intro a ha i
    have hprofile := ((mem_groupOriginals mu a z n).mp ha).2.2
    rw [crossings_eq_profileCrossings, hprofile]
    exact (hε i).1
  refine ⟨{
    member := H
    cutoff := ε
    admissible := hadmissible
    maximal := fun i => (hε i).2.1
    card_le := ?_
    moved_subset := ?_
  }⟩
  · intro i
    exact card_le_profile_of_truncation (heavySet (mu.weight H) (ε i)) i n
      (profileCrossings n i) (hε i).2.2 (profileCrossings_le_profileSize n i)
  · intro a ha i
    have hselected := ((mem_groupOriginals mu a z n).mp ha).2.1
    have hfeasible' : FeasibleFor mu a z H := fun j => ⟨ε j, hadmissible a ha j⟩
    exact selected_movedRow_subset_heavySet mu a z hselected H hfeasible' i (ε i)
      (hadmissible a ha i)

/-- The finite sets needed for counting are common to the whole actual group. -/
theorem exists_common_heavy_sets {F : Family α} (mu : MassFamily F) {s : ℕ}
    (z : Coloring α s) (n : Profile s)
    (hne : (groupOriginals mu z n).Nonempty) :
    ∃ R : Fin s → Finset α,
      (∀ i, (R i).card ≤ 2 ^ (i.val + 1) * profileSize n) ∧
      ∀ a ∈ groupOriginals mu z n, ∀ i, movedRow a z i ⊆ R i := by
  obtain ⟨w⟩ := exists_common_witness mu z n hne
  exact ⟨fun i => heavySet (mu.weight w.member) (w.cutoff i), w.card_le, w.moved_subset⟩

end TalagrandThreshold.Selector

end

end OAI
