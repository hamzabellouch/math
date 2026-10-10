import OAI.Combinatorics.BalancedRyser.Local.LocalFourEvents
import OAI.Combinatorics.BalancedRyser.Local.LocalUnusedOffsetProbability

namespace OAI

namespace Balanced.Local.UnusedOffsetProbability

noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ} {P : EqualityPattern b κ}
variable {a : DirectionAssignment F b κ} {bits : Bits b} {p : Point F}

theorem unusedPrecoverage_iff_fourEvents (M : MergedPairs F) :
    unusedPrecoverage P a bits p M ↔ FourEvents.UnusedPrecoverage P a bits p M := by
  constructor
  · rintro ⟨ij, d, hd, s, hp, hx⟩
    refine ⟨d, (PrescribedGeometry.mem_unusedDirections d).mp hd, s, hp,
      prescribedPoint P a bits M ij, ?_, hx⟩
    exact Finset.mem_image.mpr ⟨ij, Finset.mem_univ _, rfl⟩
  · rintro ⟨d, hd, s, hp, x, hxF, hx⟩
    obtain ⟨ij, _, rfl⟩ := Finset.mem_image.mp hxF
    exact ⟨ij, d, (PrescribedGeometry.mem_unusedDirections d).mpr hd, s, hp, hx⟩

omit [Field F] in
theorem offsetProbability_mono {E G : MergedPairs F → Prop}
    (h : ∀ M, E M → G M) : offsetProbability E ≤ offsetProbability G := by
  unfold offsetProbability
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro M _
  by_cases hE : E M
  · simp only [hE, h M hE, ite_true]
    exact le_rfl
  · simp only [hE, ite_false]
    positivity

theorem conditionedOffsetProbability_mono (A : MergedPairs F → Prop)
    {E G : MergedPairs F → Prop} (h : ∀ M, E M → G M) :
    conditionedOffsetProbability A E ≤ conditionedOffsetProbability A G := by
  unfold conditionedOffsetProbability
  exact div_le_div_of_nonneg_right
    (offsetProbability_mono (fun M hM => ⟨hM.1, h M hM.2⟩))
    (offsetProbability_nonneg A)

theorem conditioned_fourEvents_unusedPrecoverage_le :
    conditionedOffsetProbability (Aligned P a bits p)
      (FourEvents.UnusedPrecoverage P a bits p) ≤
      (8 * (b : ℝ) * (Fintype.card F + 1)) / (Fintype.card F : ℝ) ^ 2 := by
  have heq : FourEvents.UnusedPrecoverage P a bits p = unusedPrecoverage P a bits p := by
    funext M
    exact propext (unusedPrecoverage_iff_fourEvents M).symm
  rw [heq]
  exact conditioned_unusedPrecoverage_probability_le

theorem conditioned_admissible_precoverage_le (hE : Eligible P a) :
    conditionedOffsetProbability (Aligned P a bits p)
      (fun M => Admissible P a bits p M ∧ FourEvents.Precoverage P a bits p M) ≤
      (8 * (b : ℝ) * (Fintype.card F + 1)) / (Fintype.card F : ℝ) ^ 2 := by
  apply (conditionedOffsetProbability_mono (Aligned P a bits p) ?_).trans
    conditioned_fourEvents_unusedPrecoverage_le
  intro M hM
  exact (FourEvents.precoverage_iff_unused P a bits p M hE hM.1).mp hM.2

end
end Balanced.Local.UnusedOffsetProbability

end OAI
