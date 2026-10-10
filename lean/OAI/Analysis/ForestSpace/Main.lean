import OAI.Analysis.ForestSpace.Exhaustions

namespace OAI

open scoped BigOperators
open Finset

namespace ForestSpace

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The space
is the full continuous dual of the specified segment-norm completion, not the
coordinate completion in place of that dual. -/
theorem main_theorem :
    (¬FiniteDimensional ℝ (FullDual Vertex)) ∧
    TopologicalSpace.SeparableSpace (FullDual Vertex) ∧
    Reflexive (FullDual Vertex) ∧
    (∀ (α β : ℝ) (R : EquivalentNorm (FullDual Vertex) α β), ¬IsAUC R.N) ∧
    (∀ t : ℝ, 0 < t →
      Real.sqrt (1+t^2/12)-1 ≤ averageModulus (FullDual Vertex) norm t) ∧
    (∀ (k : ℕ) (f : (Diamond.diamond k).V → FullDual Vertex) (C : ℝ),
      Diamond.EmbeddingBound k f C → Real.sqrt (1+(k:ℝ)/12) ≤ C) := by
  exact ⟨infiniteDimensional_main_fullDual, separable_main_fullDual,
    reflexive_main_fullDual, fun _ _ R => main_no_equivalent_AUC R,
    main_average_modulus, main_diamond_distortion⟩

/-- The general-forest refinement. `ForestOrder` says that each
ancestor set is a chain; finite ancestor sets provide the rooted-forest
structure. No reflexivity or full-dual identification is assumed here. -/
theorem general_forest_main (V : Type) [PartialOrder V] [Countable V] [Infinite V]
    (hF : ForestOrder V) (hAnc : ∀ v : V, (Set.Iic v).Finite) :
    (∀ (H : Finset V) (hH : IsLowerSet (H : Set V)) (x y : X V),
      x = PX H hH x → y = QX H hH y →
      Real.sqrt (‖x‖^2+‖y‖^2/12) ≤ (‖x+y‖+‖x-y‖)/2) ∧
    (∀ (H : Finset V) (hH : IsLowerSet (H : Set V)) (x y : X V),
      x = PX H hH x → y = QX H hH y → ∀ (s t : ℝ), 0 < s → 0 < t →
      (‖x‖+s*t*‖y‖)/Real.sqrt (1+12*s^2) ≤ (‖x+t•y‖+‖x-t•y‖)/2) ∧
    (∀ t : ℝ, 0 < t → Real.sqrt (1+t^2/12)-1 ≤ averageModulus (X V) norm t) := by
  exact ⟨paired_X hF hAnc, paired_X_two_parameters hF hAnc, forest_average_modulus hF hAnc⟩

/-- The last clause of the general-forest refinement, with exactly the
scale `alpha/(2 beta)` and every equivalent norm. -/
theorem word_forest_main (α β : ℝ) (R : EquivalentNorm (X Word) α β) :
    aucModulus (X Word) R.N (α/(2*β)) = 0 :=
  word_auc_modulus_zero R

end

end ForestSpace

end OAI
