import OAI.Combinatorics.BalancedRyser.Candidates.CandidateLabelBridge
import OAI.Combinatorics.BalancedRyser.Probability.FiniteCenteredPatternLemmas

namespace OAI

namespace Balanced.CandidateExposure

noncomputable section
open scoped Classical BigOperators
open MeasureTheory TupleAlignment PartialAlignment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
local instance candidateHighMomentsMeasurableSpace : MeasurableSpace F := ⊤

theorem rootPatternModel_total_le (g : Direction F) (D : Finset (Direction F))
    (a : MergedPairs F) (m : ℕ) (hD : D.card ≤ m) :
    (rootPatternModel g).fixedExpectation D a (rootPatternModel g).count ≤
      (20480 * (m + 1) ^ 4 : ℝ) * Fintype.card F := by
  exact rootPatternModel_fixed_count_le g D a m hD

theorem rootPatternModel_overlap_le (g : Direction F) (D : Finset (Direction F))
    (a : MergedPairs F) (m : ℕ) (hD : D.card ≤ m) :
    (rootPatternModel g).fixedExpectation D a
      ((rootPatternModel g).overlapCount ∅ D) ≤ (20480 * (m + 1) ^ 4 : ℝ) := by
  exact (rootPatternModel_fixed_allExposed_overlapCount_le g D a m hD).trans
    (by nlinarith [sq_nonneg (((m : ℝ) + 1)^2)])

def centeredMomentConstant (m s : ℕ) : ℝ :=
  ((2 * s).factorial : ℝ) * 2 ^ (2 * s) *
    (2 * (20480 * ((m : ℝ) + 8 * s + 1) ^ 4)) ^ (2 * s)

theorem centeredMomentConstant_nonneg (m s : ℕ) : 0 ≤ centeredMomentConstant m s := by
  unfold centeredMomentConstant
  positivity

theorem rootPatternModel_centered_moment_le (g : Direction F)
    (K₀ : Finset (Direction F)) (a : MergedPairs F) (m s : ℕ) (hK : K₀.card ≤ m) :
    (rootPatternModel g).fixedExpectation K₀ a
      (fun M => |(rootPatternModel g).count M -
        (rootPatternModel g).fixedExpectation K₀ a (rootPatternModel g).count| ^ (2*s)) ≤
      centeredMomentConstant m s * (Fintype.card F : ℝ)^s := by
  have hq : (1 : ℝ) ≤ Fintype.card F := by
    exact_mod_cast Fintype.card_pos (α := F)
  have h := (rootPatternModel g).centered_moment_le_of_allExposedBounds
    K₀ a s 4 (Fintype.card F) (20480 * ((m : ℝ) + 8 * s + 1)^4)
    hq (by positivity) (fun b => (rootPatternModel_support_card g b).le)
    (by
      intro D hD y
      have hc : D.card ≤ m + 8*s := by omega
      convert rootPatternModel_total_le g D y (m + 8*s) hc using 1
      push_cast
      ring)
    (by
      intro D hD y
      have hc : D.card ≤ m + 8*s := by omega
      convert rootPatternModel_overlap_le g D y (m + 8*s) hc using 1
      push_cast
      ring)
  exact h

theorem conditional_successfulTupleCount_centered_moment_le (g : Direction F)
    (K₀ : Finset (Direction F)) (a : MergedPairs F) (m s : ℕ) (hK : K₀.card ≤ m) :
    (∫ M, |(successfulTupleCount g M : ℝ) -
      ∫ N, (successfulTupleCount g N : ℝ) ∂(exposedLaw K₀ a).toMeasure| ^ (2*s)
      ∂(exposedLaw K₀ a).toMeasure) ≤
      centeredMomentConstant m s * (Fintype.card F : ℝ)^s := by
  have h := rootPatternModel_centered_moment_le g K₀ a m s hK
  rw [rootPatternModel_fixedExpectation_exposed, rootPatternModel_fixed_count_exposed] at h
  simp_rw [rootPatternModel_count, ← successfulTupleCount_eq_rootSuccessCount] at h
  exact h

theorem successfulTupleCount_centered_moment_le (g : Direction F) (s : ℕ) :
    (∫ M, |(successfulTupleCount g M : ℝ) -
      ∫ N, (successfulTupleCount g N : ℝ) ∂(offsetLaw F).toMeasure| ^ (2*s)
      ∂(offsetLaw F).toMeasure) ≤
      centeredMomentConstant 0 s * (Fintype.card F : ℝ)^s := by
  have h := rootPatternModel_centered_moment_le g ∅ (fun _ _ => 0) 0 s (by simp)
  simp only [PatternModel.fixedExpectation] at h
  rw [rootPatternModel_measure] at h
  simp_rw [rootPatternModel_count, ← successfulTupleCount_eq_rootSuccessCount] at h
  exact h

end
end Balanced.CandidateExposure

end OAI
