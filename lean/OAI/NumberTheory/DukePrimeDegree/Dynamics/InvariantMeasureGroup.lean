import OAI.NumberTheory.DukePrimeDegree.Dynamics.RootBlocks

namespace OAI

/-!
# The closed group preserving a finite measure

The ambient measure stabilizer is closed. Consequently the topological
closure of the invariant root-generated group still preserves the measure.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace PrimeDegreePackets

lemma continuous_integral_rightAction {n : ℕ} (μ : Measure (X n)) [IsFiniteMeasure μ]
    (f : CompactlySupportedContinuousMap (X n) ℝ) : Continuous (fun g : G n => ∫ x, f (rightAction x g) ∂μ) := by
  apply continuous_of_dominated
    (bound := fun _ => ‖f.toBoundedContinuousFunction‖)
  · intro g
    exact (f.continuous.comp (continuous_rightAction g)).aestronglyMeasurable
  · intro g
    exact Eventually.of_forall fun x => f.toBoundedContinuousFunction.norm_coe_le_norm _
  · exact integrable_const _
  · apply Eventually.of_forall
    intro x
    apply f.continuous.comp
    induction x using Quotient.inductionOn with
    | h g =>
      exact continuous_quotient_mk'.comp (continuous_const.mul continuous_id)

lemma invariantRightSubgroup_eq_tests {n : ℕ} (μ : Measure (X n)) [IsFiniteMeasure μ] :
    (invariantRightSubgroup μ : Set (G n)) =
      ⋂ f : CompactlySupportedContinuousMap (X n) ℝ, {g | (∫ x, f (rightAction x g) ∂μ) = ∫ x, f x ∂μ} := by
  ext g
  simp only [mem_iInter, mem_ofPred_eq]
  constructor
  · intro hg f
    change μ.map (fun x => rightAction x g) = μ at hg
    have he := integral_map (μ := μ) (φ := fun x => rightAction x g)
      (f := fun x => f x) (continuous_rightAction g).measurable.aemeasurable
      f.continuous.aestronglyMeasurable
    rw [hg] at he
    exact he.symm
  · intro hg
    change μ.map (fun x => rightAction x g) = μ
    apply Measure.ext_of_integral_eq_on_compactlySupported
    intro f
    rw [integral_map (μ := μ) (f := fun x => f x)
      (continuous_rightAction g).measurable.aemeasurable
      f.continuous.aestronglyMeasurable]
    exact hg f

/-- The stabilizer of a finite measure is a closed subgroup of the real
special linear group. -/
theorem isClosed_invariantRightSubgroup {n : ℕ} (μ : Measure (X n)) [IsFiniteMeasure μ] :
    IsClosed (invariantRightSubgroup μ : Set (G n)) := by
  rw [invariantRightSubgroup_eq_tests]
  exact isClosed_iInter fun f => isClosed_eq (continuous_integral_rightAction μ f) continuous_const

/-- Closing the actual root-generated group introduces no new failure of
measure invariance. -/
theorem rootGenerated_topologicalClosure_le {n : ℕ} (μ : Measure (X n)) [IsFiniteMeasure μ] :
    (invariantRootGeneratedGroup μ).topologicalClosure ≤ invariantRightSubgroup μ := by
  exact Subgroup.topologicalClosure_minimal (invariantRootGeneratedGroup μ)
    (invariantRootGeneratedGroup_le μ)
    (isClosed_invariantRightSubgroup μ)

end PrimeDegreePackets

end

end OAI
