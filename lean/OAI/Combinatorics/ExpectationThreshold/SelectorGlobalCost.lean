import OAI.Combinatorics.ExpectationThreshold.SelectorGroupCost
import OAI.Combinatorics.ExpectationThreshold.SelectorGlobalCostProfiles
import OAI.Combinatorics.ExpectationThreshold.SelectorFeasibility
import OAI.Combinatorics.ExpectationThreshold.SelectorProfile

namespace OAI

/-!
# The global cost of actual selected moves

Partition selected pairs first by their final coloring and then by their
full profile. The profile estimate removes the profile-dependent heavy
sets before summation. Word-count normalization and the finite geometric
bound then give the strict budget under the actual coloring law.
-/

noncomputable section

open scoped BigOperators Classical

namespace TalagrandThreshold.Selector

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {F : Family α} {s : ℕ}

/-- Actual bad original colorings that select one fixed endpoint. -/
def selectedOriginals (mu : MassFamily F) (z : Coloring α s) :
    Finset (Coloring α s) := by
  classical
  exact Finset.univ.filter fun a => Bad mu a ∧ Selected mu a z

/-- Only the full profiles that occur for this endpoint. -/
def selectedProfiles (mu : MassFamily F) (z : Coloring α s) :
    Finset (Profile s) := by
  classical
  exact (selectedOriginals mu z).image fun a => profile a z

@[simp] theorem mem_selectedOriginals (mu : MassFamily F)
    (a z : Coloring α s) :
    a ∈ selectedOriginals mu z ↔ Bad mu a ∧ Selected mu a z := by
  classical
  simp only [selectedOriginals, Finset.mem_filter, Finset.mem_univ, true_and]

/-- A selected move from a bad coloring has a nonzero tuple of row sizes. -/
theorem selectedProfiles_rowCount_ne_zero (mu : MassFamily F)
    (z : Coloring α s) (n : Profile s) (hn : n ∈ selectedProfiles mu z) :
    rowCount n ≠ 0 := by
  classical
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨hbad, hselected⟩ := (mem_selectedOriginals mu a z).mp ha
  intro hz
  have hpos := Finset.card_pos.mpr (hselected.changes_nonempty hbad)
  rw [← profileSize_profile a z] at hpos
  simp only [profileSize, hz, Pi.zero_apply, Finset.sum_const_zero,
    lt_self_iff_false] at hpos

/-- Grouping by the actual full profile loses no original coloring. -/
theorem selected_endpoint_cost_grouped (mu : MassFamily F)
    (z : Coloring α s) (f : Coloring α s → ℝ) :
    (∑ a ∈ selectedOriginals mu z, f a) =
      ∑ n ∈ selectedProfiles mu z, ∑ a ∈ groupOriginals mu z n, f a := by
  classical
  have hgroup (n : Profile s) :
      (selectedOriginals mu z).filter (fun a => profile a z = n) =
        groupOriginals mu z n := by
    ext a
    simp [selectedOriginals, groupOriginals, and_assoc]
  symm
  calc
    (∑ n ∈ selectedProfiles mu z, ∑ a ∈ groupOriginals mu z n, f a) =
        ∑ n ∈ selectedProfiles mu z,
          ∑ a ∈ (selectedOriginals mu z).filter (fun a => profile a z = n), f a := by
      simp only [hgroup]
    _ = ∑ a ∈ selectedOriginals mu z, f a :=
      Finset.sum_fiberwise_of_maps_to
        (fun a ha => Finset.mem_image.mpr ⟨a, ha, rfl⟩) f

/-- Swapping the two finite sums groups all actual selected pairs by endpoint. -/
theorem selected_cost_group_by_endpoint (mu : MassFamily F)
    (f : Coloring α s → Coloring α s → ℝ) :
    (∑ a ∈ (Finset.univ : Finset (Coloring α s)).filter (Bad mu),
      ∑ z ∈ selectedMoves mu a, f a z) =
      ∑ z : Coloring α s, ∑ a ∈ selectedOriginals mu z, f a z := by
  classical
  calc
    (∑ a ∈ (Finset.univ : Finset (Coloring α s)).filter (Bad mu),
        ∑ z ∈ selectedMoves mu a, f a z) =
        ∑ a : Coloring α s, ∑ z : Coloring α s,
          if Bad mu a ∧ Selected mu a z then f a z else 0 := by
      simp only [selectedMoves, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : Bad mu a <;> simp [ha]
    _ = ∑ z : Coloring α s, ∑ a ∈ selectedOriginals mu z, f a z := by
      rw [Finset.sum_comm]
      simp only [selectedOriginals, Finset.sum_filter]

/-- All actual original colorings for one endpoint fit its probability-weighted budget. -/
theorem selected_endpoint_cost_lt (mu : MassFamily F)
    (p : ℝ) (s : ℕ) (hp : 0 < p) (hs : p * scaleSum s ≤ 1 / 2)
    (z : Coloring α s) :
    (∑ a ∈ selectedOriginals mu z, colorMass p s a * p ^ (changes a z).card) <
      colorMass p s z * (1 / 20) := by
  classical
  calc
    (∑ a ∈ selectedOriginals mu z, colorMass p s a * p ^ (changes a z).card) =
        ∑ n ∈ selectedProfiles mu z,
          ∑ a ∈ groupOriginals mu z n, colorMass p s a * p ^ (changes a z).card :=
      selected_endpoint_cost_grouped mu z _
    _ ≤ ∑ n ∈ selectedProfiles mu z,
        colorMass p s z *
          (∏ i : Fin s, (3 / (64 : ℝ) ^ (i.val + 1)) ^ (rowCount n i)) *
          (∏ i : Fin s, ((wordCount (rowCount n i) (n i) : ℝ) *
            ∏ h : Color s, colorProb p s h ^ (n i h))) :=
      Finset.sum_le_sum fun n _ => group_cost_le mu p s hp hs z n
    _ = colorMass p s z *
        (∑ n ∈ selectedProfiles mu z,
          (∏ i : Fin s, (3 / (64 : ℝ) ^ (i.val + 1)) ^ (rowCount n i)) *
          (∏ i : Fin s, ((wordCount (rowCount n i) (n i) : ℝ) *
            ∏ h : Color s, colorProb p s h ^ (n i h)))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      exact mul_assoc _ _ _
    _ < colorMass p s z * (1 / 20) :=
      mul_lt_mul_of_pos_left
        (sum_profile_weights_lt_one_twentieth p s hp hs (selectedProfiles mu z)
          (selectedProfiles_rowCount_ne_zero mu z))
        (colorMass_pos p s hp hs z)

/-- The complete selected cost is strictly below one twentieth. All grouping,
counting, reconstruction, entropy, and probability facts are proved above. -/
theorem selected_total_cost_lt_one_twentieth (mu : MassFamily F)
    (p : ℝ) (s : ℕ) (hp : 0 < p) (hs : p * scaleSum s ≤ 1 / 2) :
    (∑ a ∈ (Finset.univ : Finset (Coloring α s)).filter (Bad mu),
      ∑ z ∈ selectedMoves mu a, colorMass p s a * p ^ (changes a z).card) < 1 / 20 := by
  classical
  rw [selected_cost_group_by_endpoint]
  calc
    (∑ z : Coloring α s,
        ∑ a ∈ selectedOriginals mu z, colorMass p s a * p ^ (changes a z).card) <
        ∑ z : Coloring α s, colorMass p s z * (1 / 20) := by
      apply Finset.sum_lt_sum_of_nonempty
        ⟨(fun _ => Fin.last s), Finset.mem_univ _⟩
      intro z _
      exact selected_endpoint_cost_lt mu p s hp hs z
    _ = 1 / 20 := by
      rw [← Finset.sum_mul, sum_colorMass, one_mul]

/-- The same bound in expectation notation, ready for the bad-event argument. -/
theorem weighted_bad_selected_cost_le (mu : MassFamily F)
    (p : ℝ) (s : ℕ) (hp : 0 < p) (hs : p * scaleSum s ≤ 1 / 2) :
    (∑ a : Coloring α s, if Bad mu a then
      colorMass p s a * ∑ z ∈ selectedMoves mu a, p ^ (changes a z).card else 0) ≤ 1 / 20 := by
  classical
  simpa only [Finset.sum_filter, Finset.mul_sum] using
    (selected_total_cost_lt_one_twentieth mu p s hp hs).le

end TalagrandThreshold.Selector

end

end OAI
