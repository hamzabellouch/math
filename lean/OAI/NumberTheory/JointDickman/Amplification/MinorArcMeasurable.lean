import OAI.NumberTheory.JointDickman.Arithmetic.SmoothCoefficientMinorArc
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

namespace OAI

/-! # The measurable discarded minor-arc region -/

namespace JointDickman

noncomputable def minorArcRegion (B j : ℕ) (X : ℝ) : Set ℝ :=
  {θ | θ ∈ Set.Ioc 0 1 ∧ ¬ InRationalArc (-(j : ℝ)*θ) ((B : ℝ)^12) ((B : ℝ)^13/X)}

theorem measurableSet_rationalArcs (Q δ : ℝ) : MeasurableSet {θ | InRationalArc θ Q δ} := by
  have he : {θ | InRationalArc θ Q δ} =
      ⋃ r : ℚ, {θ : ℝ | (r.den : ℝ) ≤ Q ∧ |θ-(r : ℝ)| ≤ δ} := by
    ext θ
    simp [InRationalArc]
  rw [he]
  apply MeasurableSet.iUnion
  intro r
  by_cases hr : (r.den : ℝ) ≤ Q
  · simp only [hr,true_and]
    exact isClosed_le (continuous_id.sub continuous_const).abs continuous_const |>.measurableSet
  · simp only [hr,false_and,Set.ofPred_false]
    exact MeasurableSet.empty

theorem minorArcRegion_measurable (B j : ℕ) (X : ℝ) : MeasurableSet (minorArcRegion B j X) := by
  exact measurableSet_Ioc.inter
    (((measurableSet_rationalArcs ((B : ℝ)^12) ((B : ℝ)^13/X)).preimage
      (continuous_const.mul continuous_id).measurable).compl)

theorem minorArcRegion_subset (B j : ℕ) (X : ℝ) : minorArcRegion B j X ⊆ Set.Ioc 0 1 :=
  fun _ h => h.1

end JointDickman

end OAI
