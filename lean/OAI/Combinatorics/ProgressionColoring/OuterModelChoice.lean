import OAI.Combinatorics.ProgressionColoring.OuterChoiceDefinitions
import OAI.Combinatorics.ProgressionColoring.ConstructionWordFamily
import OAI.Combinatorics.ProgressionColoring.EligibleOuterColoring
import OAI.Combinatorics.ProgressionColoring.OuterBudget

namespace OAI

noncomputable section

open Filter
open scoped BigOperators

namespace QuantitativeVanDerWaerden.ConstructionModel

open Parameters

/-- One eventual range works for every admissible prime-power choice. The
finite word count, scale inequalities, and probability budget are all supplied
by the actual construction rather than assumed of the selected coloring. -/
theorem eventually_outerChoice :
    ∀ᶠ k : ℕ in atTop, ∃ hk : 3 ≤ k, ∀ s : Data k, Nonempty (OuterChoice s hk) := by
  filter_upwards [eventually_ge_atTop (32 : ℕ), eventually_geometryScales,
    eventually_outer_counted_budget] with k hk32 hgeom hbudget
  have hk : 3 ≤ k := by omega
  have hk1 : 1 ≤ k := by omega
  refine ⟨hk, ?_⟩
  intro s
  obtain ⟨words, hwords, hcard⟩ := exists_fullLabelWord_family s hk
  let F : ℝ := ((uniformCount k + Fintype.card (mesh s hk).Label : ℕ) : ℝ)
  have hL : (1 : ℝ) ≤ lambda k := by
    exact_mod_cast (Nat.succ_le_of_lt (lambda_pos k))
  have hF : (1 : ℝ) ≤ F := by
    dsimp [F]
    exact_mod_cast ((Nat.succ_le_of_lt (uniformCount_pos hk)).trans
      (Nat.le_add_right (uniformCount k) (Fintype.card (mesh s hk).Label)))
  have hLlog : Real.log (lambda k : ℝ) ≤
      (dimension k : ℝ) ^ 2 * Real.log (2 * (cutoff k : ℝ)) := by
    calc
      Real.log (lambda k : ℝ) ≤
          ((dimension k ^ 2 : ℕ) : ℝ) * Real.log (2 * (cutoff k : ℝ)) :=
        log_dilation_le (h₀ := dimension k ^ 2) (cutoff_pos hk1)
      _ = (dimension k : ℝ) ^ 2 * Real.log (2 * (cutoff k : ℝ)) :=
        congrArg (fun x : ℝ => x * Real.log (2 * (cutoff k : ℝ)))
          (Nat.cast_pow (dimension k) 2)
  have hmesh : F ≤ (k : ℝ) ^ 2 * (lambda k : ℝ) +
      28 * (k : ℝ) ^ 3 * Real.log k := by
    dsimp [F]
    rw [Nat.cast_add, uniformCount, Nat.cast_mul, Nat.cast_pow]
    exact add_le_add_right (card_second_labels_le s hk) _
  have hcount : (words.card : ℝ) ≤
      (16 * (3 * (k : ℝ) ^ 2 * F + 1) ^ (6 : ℕ)) ^ (2 * dimension k) := by
    dsimp [F]
    exact_mod_cast hcard
  have hbudget' := hbudget (lambda k) F hL hF words.card hLlog hmesh hcount
  have hMkR : (cutoff k : ℝ) ≤ k := by
    have htwo := hgeom.two_cutoff_le_length
    have hnonneg : (0 : ℝ) ≤ cutoff k := Nat.cast_nonneg _
    linarith
  have hMk : cutoff k ≤ k := by exact_mod_cast hMkR
  have hperiod : ∀ h ∈ Finset.Ioc (dimension k ^ 2) (2 * cutoff k), 200 ≤ h := by
    intro h hh
    have hD2R : (200 : ℝ) ≤ (dimension k : ℝ) ^ 2 := by
      have := hgeom.local_event_size
      linarith
    have hD2 : 200 ≤ dimension k ^ 2 := by exact_mod_cast hD2R
    exact hD2.trans (Finset.mem_Ioc.mp hh).1.le
  obtain ⟨color, hbalanced⟩ := exists_outer_balanced
    (uniformCount k) (uniformCount_pos hk) (mesh s hk) (lambda k) (cutoff k)
    (dimension_pos hk1) (cutoff_pos hk1) hMk words
    (Finset.Ioc (dimension k ^ 2) (2 * cutoff k))
    hgeom.light_row_size hperiod hbudget'
  exact ⟨⟨words, color, hwords, hcard, hbalanced⟩⟩

/-- Absolute threshold form of the actual outer-coloring choice. It is chosen
before the prime scale or any requested number of final colors. -/
theorem exists_outerChoice_threshold :
    ∃ K : ℕ, 32 ≤ K ∧ ∀ k ≥ K, ∃ hk : 3 ≤ k,
      ∀ s : Data k, Nonempty (OuterChoice s hk) := by
  obtain ⟨K, hK⟩ := eventually_atTop.1
    ((eventually_ge_atTop (32 : ℕ)).and eventually_outerChoice)
  exact ⟨K, (hK K le_rfl).1, fun k hk => (hK k hk).2⟩

end QuantitativeVanDerWaerden.ConstructionModel

end

end OAI
