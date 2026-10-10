import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.InitialFamily
import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.ConstructionLabels

namespace OAI

/-! Tensor extraction over arbitrary fields and its asymptotic rate. -/

noncomputable section

namespace MatrixMultiplication.AllFieldInitialChoice

open MatrixMultiplication.Foundation AllFieldHistory AllFieldFiniteFamily Filter
open scoped BigOperators Topology Classical

variable {K : ℕ}

structure Choice (allocation : Allocation) (m : ℕ) (δ : ℝ) where
  sample : AllFieldInitialFamily.Sample (K := K) allocation
    (δ / (AllFieldInitialFamily.grid (K := K) allocation : ℝ)) m
  selected : Finset (JointPopulation.Target (initialJointCounts (K := K) allocation m))
  card_selected : selected.card = AllFieldConstructionRates.initialCount (K := K) allocation δ m
  good : ∀ e ∈ selected, AllFieldInitialFamily.Good allocation
    (δ / (AllFieldInitialFamily.grid (K := K) allocation : ℝ)) m sample e

theorem initial_count_eq (allocation : Allocation) (m : ℕ) (δ : ℝ) :
    ⌊Real.exp ((populationLength (K := K) allocation m : ℝ) *
      ((K : ℝ) * AllFieldInitialEntropy.nativeH0 -
        δ / (AllFieldInitialFamily.grid (K := K) allocation : ℝ)))⌋₊ =
      AllFieldConstructionRates.initialCount (K := K) allocation δ m := by
  rw [AllFieldConstructionRates.initialCount_eq,
    AllFieldInitialFamily.populationLength_eq_mul_grid, Nat.cast_mul]
  congr 2
  change ((m : ℝ) * (AllFieldInitialFamily.grid (K := K) allocation : ℝ)) *
      ((K : ℝ) * AllFieldInitialEntropy.nativeH0 -
        δ / (AllFieldInitialFamily.grid (K := K) allocation : ℝ)) =
    (m : ℝ) * ((AllFieldInitialFamily.grid (K := K) allocation : ℝ) *
      ((K : ℝ) * AllFieldInitialEntropy.nativeH0) - δ)
  have hD : (AllFieldInitialFamily.grid (K := K) allocation : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (AllFieldInitialFamily.grid_pos allocation).ne'
  field_simp [hD]

theorem eventually_nonempty (allocation : Allocation) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ m : ℕ in atTop, Nonempty (Choice (K := K) allocation m δ) := by
  have hs : 0 < δ / (AllFieldInitialFamily.grid (K := K) allocation : ℝ) :=
    div_pos hδ (Nat.cast_pos.mpr (AllFieldInitialFamily.grid_pos allocation))
  have h := AllFieldInitialFamily.eventually_exists_execution_with_width
    (K := K) allocation ℚ 0 hs
  filter_upwards [h] with m hm
  obtain ⟨sample, selected, hcard, hgood, _execution⟩ := hm
  exact ⟨{
    sample := sample
    selected := selected
    card_selected := hcard.trans (initial_count_eq allocation m δ)
    good := hgood }⟩

abbrev Tags (allocation : Allocation) (m : ℕ) (δ : ℝ)
    (choice : Choice (K := K) allocation m δ) :=
  AllFieldInitialHash.SelectedTargets (initialJointCounts (K := K) allocation m)
    choice.selected

@[simp] theorem card_tags (allocation : Allocation) (m : ℕ) (δ : ℝ)
    (choice : Choice (K := K) allocation m δ) :
    Fintype.card (Tags allocation m δ choice) =
      AllFieldConstructionRates.initialCount (K := K) allocation δ m := by
  rw [AllFieldInitialHash.selectedTargets_card]
  exact choice.card_selected

def execution (allocation : Allocation) (m : ℕ) (δ : ℝ)
    (choice : Choice (K := K) allocation m δ) (F : Type*) [Field F] (ε : ℝ) :
    Execution (cwSource F K (populationLength (K := K) allocation m))
      (Tensor.directSum (fun _ : Tags allocation m δ choice =>
        stateTensor F (K := K) allocation m ε 0)) :=
  AllFieldInitialFamily.executionWithWidth allocation F
    (δ / (AllFieldInitialFamily.grid (K := K) allocation : ℝ)) ε m
    choice.sample choice.selected choice.good

@[simp] theorem execution_copies (allocation : Allocation) (m : ℕ) (δ : ℝ)
    (choice : Choice (K := K) allocation m δ) (F : Type*) [Field F] (ε : ℝ) :
    Fintype.card (execution allocation m δ choice F ε).Copies = 1 := rfl

end MatrixMultiplication.AllFieldInitialChoice

end

end OAI
