import OAI.Analysis.Nonexpansive.OrderedTree
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.NormNum

namespace OAI

/-!
# Budgets attached to retained candidate ordinals

The label of a retained node is its zero-based ordinal in the global candidate
sequence.  Thus the one-based label `ℓ = label + 1` gives the budget
`2 ^ (-ℓ - 8) = (1 / 2) ^ (label + 9)`.  Injectivity, rather than a new
enumeration of retained nodes, compares their total with the candidate series.
The actual tree construction supplies this label and its injectivity proof.
-/

noncomputable section

open scoped BigOperators

namespace ReflexiveFixedPoints

/-- The dyadic budget of the candidate with zero-based ordinal `n`. -/
def candidateBudget (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ (n + 9)

theorem candidateBudget_pos (n : ℕ) : 0 < candidateBudget n := by
  exact pow_pos (by norm_num : (0 : ℝ) < 1 / 2) _

theorem candidateBudget_nonneg (n : ℕ) : 0 ≤ candidateBudget n :=
  (candidateBudget_pos n).le

theorem candidateBudget_le_one (n : ℕ) : candidateBudget n ≤ 1 := by
  exact pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)

/-- The complete candidate series has sum exactly `1 / 256`. -/
theorem hasSum_candidateBudget : HasSum candidateBudget (1 / 256 : ℝ) := by
  have h := HasSum.mul_right ((1 / 2 : ℝ) ^ 9) hasSum_geometric_two
  change HasSum (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 9)) (1 / 256 : ℝ)
  simpa only [candidateBudget, pow_add] using
    (show HasSum (fun n : ℕ => (1 / 2 : ℝ) ^ n * (1 / 2 : ℝ) ^ 9)
      (1 / 256 : ℝ) from by convert! h using 1; norm_num)

theorem summable_candidateBudget : Summable candidateBudget :=
  hasSum_candidateBudget.summable

theorem tsum_candidateBudget : (∑' n, candidateBudget n) = (1 / 256 : ℝ) :=
  hasSum_candidateBudget.tsum_eq

namespace OrderedTree

/-- Every nonroot node, retaining its actual positive level. -/
abbrev NonrootNode (T : OrderedTree) := Σ k : ℕ, T.Node (k + 1)

variable {T : OrderedTree}

/-- The retained budget uses the original global candidate label. -/
def retainedBudget (label : T.NonrootNode → ℕ) (v : T.NonrootNode) : ℝ :=
  candidateBudget (label v)

theorem retainedBudget_pos (label : T.NonrootNode → ℕ) (v : T.NonrootNode) :
    0 < retainedBudget label v :=
  candidateBudget_pos (label v)

theorem retainedBudget_nonneg (label : T.NonrootNode → ℕ) (v : T.NonrootNode) :
    0 ≤ retainedBudget label v :=
  (retainedBudget_pos label v).le

theorem retainedBudget_le_one (label : T.NonrootNode → ℕ) (v : T.NonrootNode) :
    retainedBudget label v ≤ 1 :=
  candidateBudget_le_one (label v)

/-- Retaining a subset of globally distinct candidate labels preserves
summability.  No bound on the number of nodes at later levels is needed. -/
theorem summable_retainedBudget (label : T.NonrootNode → ℕ)
    (hlabel : Function.Injective label) : Summable (retainedBudget label) := by
  exact summable_candidateBudget.comp_injective hlabel

/-- The total retained budget is at most the complete candidate budget. -/
theorem tsum_retainedBudget_le (label : T.NonrootNode → ℕ)
    (hlabel : Function.Injective label) :
    (∑' v, retainedBudget label v) ≤ (1 / 256 : ℝ) := by
  calc
    (∑' v, retainedBudget label v) ≤ ∑' n, candidateBudget n := by
      exact tsum_comp_le_tsum_of_inj summable_candidateBudget candidateBudget_nonneg hlabel
    _ = (1 / 256 : ℝ) := tsum_candidateBudget

theorem tsum_retainedBudget_le_one_div_128 (label : T.NonrootNode → ℕ)
    (hlabel : Function.Injective label) :
    (∑' v, retainedBudget label v) ≤ (1 / 128 : ℝ) := by
  exact (tsum_retainedBudget_le label hlabel).trans (by norm_num)

/-- Every finite retained selection satisfies the same global budget bound. -/
theorem sum_retainedBudget_le (label : T.NonrootNode → ℕ)
    (hlabel : Function.Injective label) (s : Finset T.NonrootNode) :
    (∑ v ∈ s, retainedBudget label v) ≤ (1 / 256 : ℝ) := by
  calc
    (∑ v ∈ s, retainedBudget label v) ≤ ∑' v, retainedBudget label v :=
      (summable_retainedBudget label hlabel).sum_le_tsum s
        (fun v _ => retainedBudget_nonneg label v)
    _ ≤ (1 / 256 : ℝ) := tsum_retainedBudget_le label hlabel

/-- A finite truncation, or any finite injectively indexed collection of
actual nonroot nodes, satisfies the complete retained budget bound. -/
theorem sum_retainedBudget_comp_le {ι : Type*} [Fintype ι]
    (label : T.NonrootNode → ℕ) (hlabel : Function.Injective label)
    (node : ι → T.NonrootNode) (hnode : Function.Injective node) :
    (∑ i, retainedBudget label (node i)) ≤ (1 / 256 : ℝ) := by
  calc
    (∑ i, retainedBudget label (node i)) = ∑' i, retainedBudget label (node i) :=
      (tsum_fintype _).symm
    _ ≤ ∑' v, retainedBudget label v :=
      tsum_comp_le_tsum_of_inj (summable_retainedBudget label hlabel)
        (retainedBudget_nonneg label) hnode
    _ ≤ (1 / 256 : ℝ) := tsum_retainedBudget_le label hlabel

end OrderedTree
end ReflexiveFixedPoints

end

end OAI
